# -*- coding: utf-8 -*-
"""
xfile_importer.py - Maya 2022 DirectX XFile (.x) 导入插件（单文件版）
【无蒙皮版本（保留骨骼）· 性能优化版】
- 按 X 文件 SkinWeights 引用的骨骼名创建 Maya joint，层级严格按 Frame 结构
- 不创建 skinCluster，网格与骨骼之间无蒙皮绑定
- 所有网格挂到所属 Frame 下，顶点不做任何预乘/变换，保持 X 文件原始坐标
- 名字尽量保留原名（只处理 Maya 不接受的字符和重名冲突）
- 骨骼-mesh 绑定关系查看（导入时自动缓存 + 打印；查看器优先用缓存）

性能优化（相对上一版）：
  ① 纹理搜索改为一次性索引（_build_tex_index 从"已定义未使用"变为全程使用）
  ② UV fallback 增加 per-face bulk（大量减少 API 调用）
  ③ [DEBUG] 打印受 _VERBOSE 控制
  ④ 骨骼绑定打印拆两级（默认只打一行汇总，完整列表 UI 查看）
  ⑤ optionVar 读取加 1 元缓存
  ⑥ XML 材质模糊匹配长名优先
  ⑦ _find_texture / _inject_xml_materials 全面提速

整合 4 个模块：
  ├── Section 1 ── XFileParser（纯 Python，txt/bin/tzip/bzip）
  ├── Section 2 ── Scene builder（cmds + MFnMesh + 后处理）
  ├── Section 3 ── import_x_file（调用入口）
  ├── Section 4 ── MPxFileTranslator
  ├── Section 5 ── UI + 菜单
  └── Section 6 ── Plugin entry

安装：放到 Maya plug-ins 目录。
使用：菜单栏 → DirectX → Import X File...
      或 File → Import → "DirectX XFile Importer"
"""

from __future__ import annotations

import math
import os
import re
import struct
import traceback
import zlib
from warnings import warn
from collections import defaultdict

import maya.cmds as cmds
import maya.mel as mel
import maya.OpenMayaMPx as OpenMayaMPx
import maya.api.OpenMaya as om

# 顶部 import 区域之后
_VERBOSE = False
def _vprint(*args):
    if _VERBOSE:
        print(*args)

# ===========================================================================
# Section 1: XFileParser
# ===========================================================================

MSZIP_MAGIC = 0x4B43
MSZIP_BLOCK = 32768
AI_MAX_NUMBER_OF_TEXTURECOORDS = 2
AI_MAX_NUMBER_OF_COLOR_SETS = 1
_XFILE_MATERIAL_CACHE = {}   # (name, base_path) -> (shader, sg)
_IMPORT_CUSTOM_NORMALS = False  # 默认关闭，使用 Maya 自动算法线（解决黑斑）

# 导入时是否在控制台打印骨骼-mesh 绑定关系（缓存仍会填充，供查看器使用）
_PRINT_BONE_BINDINGS = False
# True = 打印完整双向列表（啰嗦、慢）；False = 只打一行汇总（快、清爽）
# 完整列表随时可在 UI/菜单的 "View Bone Bindings..." 查看
_PRINT_BONE_BINDINGS_VERBOSE = False

# 【新增】最近一次导入/查看的骨骼绑定缓存
# 结构：{'path': str, 'text': str}，None 表示还没导入过任何 X 文件
_LAST_BONE_BINDINGS = None


class Face:
    def __init__(self):
        self.indices = []


class TexEntry:
    def __init__(self, name='', isNormalMap=False):
        self.name = name
        self.isNormalMap = isNormalMap


class Material:
    def __init__(self):
        self.name = ''
        self.isReference = False
        self.diffuse = (0.0, 0.0, 0.0, 1.0)
        self.specularExponent = 0.0
        self.specular = (0.0, 0.0, 0.0)
        self.emissive = (0.0, 0.0, 0.0)
        self.textures = []
        self.sceneIndex = -1
        self.xml_props = {}


class BoneWeight:
    def __init__(self):
        self.vertex = 0
        self.weight = 0.0


class Bone:
    def __init__(self):
        self.name = ''
        self.weights = []
        self.offsetMatrix = ()


class Mesh:
    def __init__(self):
        self.positions = []
        self.posFaces = []
        self.normals = []
        self.normalFaces = []
        self.numTextures = 0
        self.texCoords = []
        self.numColorSets = 0
        self.colors = []
        self.faceMaterials = []
        self.materials = []
        self.bones = []


class Node:
    def __init__(self, parent=None):
        self.name = ''
        self.trafoMatrix = ()
        self.parent = parent
        self.children = []
        self.meshes = []


class AnimBone:
    def __init__(self):
        self.boneName = ''
        self.posKeys = []
        self.rotKeys = []
        self.scaleKeys = []
        self.trafoKeys = []


class Animation:
    def __init__(self):
        self.name = ''
        self.anims = []


class Scene:
    def __init__(self):
        self.rootNode = None
        self.globalMeshes = []
        self.globalMaterials = []
        self.anims = []
        self.animTicksPerSecond = 0


class XFileParser:
    def __init__(self, buffer):
        self.majorVersion = 0
        self.minorVersion = 0
        self.isBinaryFormat = False
        self.binaryFloatSize = 0
        self.binaryNumCount = 0
        self.p = 0
        self.end = len(buffer)
        self.buffer = buffer
        self.lineNumber = 0
        self.scene = Scene()
        self.isCompressed = False

        if len(buffer) < 16 or buffer[0:4] != b'xof ':
            self._throw('Header mismatch, file is not an XFile.')

        try:
            self.majorVersion = int(buffer[4:6])
            self.minorVersion = int(buffer[6:8])
        except ValueError:
            self._throw('Invalid version in XFile header.')

        compressed = False
        fmt = buffer[8:12]
        if fmt == b'txt ':
            self.isBinaryFormat = False
        elif fmt == b'bin ':
            self.isBinaryFormat = True
        elif fmt == b'tzip':
            self.isBinaryFormat = False
            compressed = True
            self.isCompressed = True     # ← 新增
        elif fmt == b'bzip':
            self.isBinaryFormat = True
            compressed = True
            self.isCompressed = True     # ← 新增
        else:
            self._throw('Unsupported xfile format: %r' % fmt)

        try:
            self.binaryFloatSize = int(buffer[12:16])
        except ValueError:
            self._throw('Invalid float size in XFile header.')
        if self.binaryFloatSize not in (32, 64):
            self._throw('Unknown float size %d.' % self.binaryFloatSize)

        self.p = 16
        if compressed:
            self._decompress()
        else:
            self._read_until_eol()

        self.parse_file()

    def _decompress(self):
        """[MSZIP v3-final] 解压 MSZIP 压缩的 XFile。

        - ofs 语义 = 数据长度（MudRunner 变体，自适应检测）
        - 跨块字典：block N 用 block N-1 最后 32KB 作为 zdict
        - 末尾截断兜底：actual_size = min(ofs, available)，不报 truncated
        """
        if self.end < 22:
            self._throw('Compressed file too short (%d bytes, need >= 22)'
                        % self.end)

        self.p = 22
        if self.p >= self.end:
            self._throw('Compressed file has no data after compression header')

        chunks = []
        block_idx = 0
        data_size_mode = None
        prev_data = b''
        truncated_blocks = 0

        while self.p + 4 <= self.end:
            ofs = struct.unpack_from('<H', self.buffer, self.p)[0]
            magic = struct.unpack_from('<H', self.buffer, self.p + 2)[0]

            if magic != MSZIP_MAGIC:
                if block_idx > 0:
                    break
                self._throw(
                    'MSZIP block %d: bad magic 0x%04X at offset %d '
                    '(expected 0x%04X "CK")'
                    % (block_idx, magic, self.p, MSZIP_MAGIC))

            if ofs < 4:
                self._throw('MSZIP block %d: invalid size %d (< 4)'
                            % (block_idx, ofs))

            ds = self.p + 4
            available = self.end - ds

            if data_size_mode == 'direct':
                candidates = [('direct', ofs)]
            elif data_size_mode == 'standard':
                candidates = [('standard', ofs - 4)]
            elif data_size_mode == 'minus2':
                candidates = [('minus2', ofs - 2)]
            else:
                candidates = [('direct', ofs),
                              ('standard', ofs - 4),
                              ('minus2', ofs - 2)]

            decompressed = None
            used_size = None
            used_mode = None
            last_err = None
            was_truncated = False

            for mode_name, declared_size in candidates:
                if declared_size <= 0:
                    continue
                # 【兜底】末尾截断：用实际可用字节
                actual_size = min(declared_size, available)
                if actual_size <= 0:
                    last_err = 'no data'
                    continue

                zdict = prev_data[-32768:] if prev_data else None
                try:
                    if zdict:
                        d = zlib.decompressobj(-15, zdict=zdict)
                    else:
                        d = zlib.decompressobj(-15)
                    out = d.decompress(self.buffer[ds:ds + actual_size])
                    out += d.flush()
                    decompressed = out
                    used_size = actual_size
                    used_mode = mode_name
                    was_truncated = (actual_size < declared_size)
                    break
                except zlib.error as e:
                    last_err = e
                    continue

            if decompressed is None:
                self._throw(
                    'MSZIP block %d: decompress failed '
                    '(ofs=%d at offset=%d, mode=%r, available=%d): %s'
                    % (block_idx, ofs, self.p, data_size_mode,
                       available, last_err))

            if data_size_mode is None:
                data_size_mode = used_mode
                print('[xfile_importer] MSZIP mode: %s '
                      '(block 0 ofs=%d, data_size=%d)'
                      % (used_mode, ofs, used_size))

            if was_truncated:
                truncated_blocks += 1
                print('[xfile_importer] MSZIP block %d: truncated at EOF '
                      '(declared %d, available %d, got %d bytes)'
                      % (block_idx, ofs, used_size, len(decompressed)))

            chunks.append(decompressed)
            prev_data = decompressed
            self.p = ds + used_size
            block_idx += 1

            if was_truncated:
                break

        if not chunks:
            self._throw('No MSZIP blocks decompressed (file may be empty)')

        self.buffer = b''.join(chunks)
        self.end = len(self.buffer)
        self.p = 0
        print('[xfile_importer] MSZIP: %d block(s) -> %d bytes '
              '(%d truncated at EOF)'
              % (block_idx, self.end, truncated_blocks))


    def parse_file(self):
        while True:
            name = self._next_token()
            if not name:
                break
            if name == b'template':
                self._parse_template()
            elif name == b'Frame':
                self._parse_frame()
            elif name == b'Mesh':
                self.scene.globalMeshes.append(self._parse_mesh())
            elif name == b'AnimTicksPerSecond':
                self._parse_anim_ticks()
            elif name == b'AnimationSet':
                self._parse_animation_set()
            elif name == b'Material':
                self.scene.globalMaterials.append(self._parse_material())
            elif name == b'}':
                warn('Unexpected } at top level')
            else:
                warn('Unknown top-level object: %r' % name)
                self._skip_unknown()

    def _parse_template(self):
        self._read_head()
        self._next_token()
        while True:
            s = self._next_token()
            if not s:
                self._throw('Unexpected EOF in template')
            if s == b'}':
                return

    def _parse_frame(self, parent=None):
        name = self._read_head()
        node = Node(parent)
        node.name = name.decode('utf-8', errors='replace')

        if parent is not None:
            parent.children.append(node)
        else:
            if self.scene.rootNode is not None:
                ex = self.scene.rootNode
                if ex.name != '$dummy_root':
                    dummy = Node()
                    dummy.name = '$dummy_root'
                    self.scene.rootNode = dummy
                    dummy.children.append(ex)
                    ex.parent = dummy
                self.scene.rootNode.children.append(node)
                node.parent = self.scene.rootNode
            else:
                self.scene.rootNode = node

        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in frame')
            if obj == b'}':
                break
            elif obj == b'Frame':
                self._parse_frame(node)
            elif obj == b'FrameTransformMatrix':
                node.trafoMatrix = self._parse_matrix()
            elif obj == b'Mesh':
                node.meshes.append(self._parse_mesh())
            else:
                warn('Unknown object in frame: %r' % obj)
                self._skip_unknown()

    def _parse_matrix(self):
        self._read_head()
        vals = tuple(self._read_float() for _ in range(16))
        self._check_semicolon()
        self._check_closing_brace()
        return vals

    def _parse_mesh(self):
        mesh = Mesh()
        self._read_head()

        n = self._read_int()
        for _ in range(n):
            mesh.positions.append(self._read_vec3())

        nf = self._read_int()
        for fi in range(nf):
            cnt = self._read_int()
            if cnt < 3:
                self._throw('Invalid index count %d for face %d' % (cnt, fi))
            face = Face()
            for _ in range(cnt):
                face.indices.append(self._read_int())
            mesh.posFaces.append(face)
            self._test_separator()

        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in mesh')
            elif obj == b'}':
                break
            elif obj == b'MeshNormals':
                self._parse_mesh_normals(mesh)
            elif obj == b'MeshTextureCoords':
                self._parse_mesh_uv(mesh)
            elif obj == b'MeshVertexColors':
                self._parse_mesh_vertex_colors(mesh)
            elif obj == b'MeshMaterialList':
                self._parse_mesh_materials(mesh)
            elif obj == b'VertexDuplicationIndices':
                self._skip_unknown()
            elif obj == b'XSkinMeshHeader':
                self._parse_skin_header(mesh)
            elif obj == b'SkinWeights':
                self._parse_skin_weights(mesh)
            else:
                warn('Unknown object in mesh: %r' % obj)
                self._skip_unknown()
        return mesh

    def _parse_mesh_normals(self, mesh):
        self._read_head()
        n = self._read_int()
        for _ in range(n):
            mesh.normals.append(self._read_vec3())
        nf = self._read_int()
        if nf != len(mesh.posFaces):
            self._throw('Normal face count does not match vertex face count.')
        for _ in range(nf):
            cnt = self._read_int()
            face = Face()
            for _ in range(cnt):
                face.indices.append(self._read_int())
            mesh.normalFaces.append(face)
            self._test_separator()
        self._check_closing_brace()

    def _parse_mesh_uv(self, mesh):
        self._read_head()
        if mesh.numTextures + 1 > AI_MAX_NUMBER_OF_TEXTURECOORDS:
            self._throw('Too many sets of texture coordinates')
        n = self._read_int()
        if n != len(mesh.positions):
            self._throw('Texture coord count does not match vertex count')
        mesh.texCoords.append([self._read_vec2() for _ in range(n)])
        mesh.numTextures += 1
        self._check_closing_brace()

    def _parse_mesh_vertex_colors(self, mesh):
        self._read_head()
        if mesh.numColorSets + 1 > AI_MAX_NUMBER_OF_COLOR_SETS:
            self._throw('Too many colorsets')
        if mesh.numColorSets >= len(mesh.colors):
            mesh.colors.append([])
        colors = mesh.colors[mesh.numColorSets]
        mesh.numColorSets += 1
        n = self._read_int()
        if n != len(mesh.positions):
            self._throw('Vertex color count does not match vertex count')
        colors.extend([(0.0, 0.0, 0.0, 1.0)] * n)
        for _ in range(n):
            idx = self._read_int()
            if idx >= len(mesh.positions):
                self._throw('Vertex color index out of bounds')
            colors[idx] = self._read_rgba()
            if not self.isBinaryFormat and self.buffer[self.p:self.p + 1] in (b';', b','):
                self.p += 1
        self._check_closing_brace()

    def _parse_mesh_materials(self, mesh):
        self._read_head()
        self._read_int()
        n = self._read_int()
        if n != len(mesh.posFaces) and n != 1:
            self._throw('Per-face material index count does not match face count.')
        for _ in range(n):
            mesh.faceMaterials.append(self._read_int())
        if not self.isBinaryFormat and self.p < self.end and self.buffer[self.p:self.p + 1] == b';':
            self.p += 1
        while len(mesh.faceMaterials) < len(mesh.posFaces):
            mesh.faceMaterials.append(mesh.faceMaterials[0])
        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in material list')
            elif obj == b'}':
                break
            elif obj == b'{':
                mat_name = self._next_token()
                mat = Material()
                mat.isReference = True
                mat.name = mat_name.decode('utf-8', errors='replace')
                mesh.materials.append(mat)
                self._check_closing_brace()
            elif obj == b'Material':
                mesh.materials.append(self._parse_material())
            elif obj == b';':
                pass
            else:
                warn('Unknown object in material list: %r' % obj)
                self._skip_unknown()

    def _parse_material(self):
        mat = Material()
        name = self._read_head()
        if not name:
            name = ('material_%d' % self.lineNumber).encode()
        mat.name = name.decode('utf-8', errors='replace')
        mat.isReference = False
        mat.diffuse = self._read_rgba()
        mat.specularExponent = self._read_float()
        mat.specular = self._read_rgb()
        mat.emissive = self._read_rgb()
        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in material')
            elif obj == b'}':
                break
            elif obj in (b'TextureFilename', b'TextureFileName'):
                mat.textures.append(TexEntry(self._parse_texture_filename()))
            elif obj in (b'NormalmapFilename', b'NormalmapFileName'):
                mat.textures.append(TexEntry(self._parse_texture_filename(), True))
            else:
                warn('Unknown object in material: %r' % obj)
                self._skip_unknown()
        return mat

    def _parse_anim_ticks(self):
        self._read_head()
        self.scene.animTicksPerSecond = self._read_int()
        self._check_closing_brace()

    def _parse_animation_set(self):
        name = self._read_head()
        anim = Animation()
        anim.name = name.decode('utf-8', errors='replace')
        self.scene.anims.append(anim)
        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in animation set')
            elif obj == b'}':
                break
            elif obj == b'Animation':
                self._parse_animation(anim)
            else:
                warn('Unknown object in animation set: %r' % obj)
                self._skip_unknown()

    def _parse_animation(self, anim):
        self._read_head()
        banim = AnimBone()
        anim.anims.append(banim)
        while True:
            obj = self._next_token()
            if not obj:
                self._throw('Unexpected EOF in animation')
            elif obj == b'}':
                break
            elif obj == b'AnimationKey':
                self._parse_animation_key(banim)
            elif obj == b'AnimationOptions':
                self._skip_unknown()
            elif obj == b'{':
                banim.boneName = self._next_token().decode('utf-8', errors='replace')
                self._check_closing_brace()
            else:
                warn('Unknown object in animation: %r' % obj)
                self._skip_unknown()

    def _parse_animation_key(self, banim):
        self._read_head()
        ktype = self._read_int()
        n = self._read_int()
        for _ in range(n):
            t = float(self._read_int())
            if ktype == 0:
                if self._read_int() != 4:
                    self._throw('Invalid quaternion key')
                w = self._read_float(); x = self._read_float()
                y = self._read_float(); z = self._read_float()
                banim.rotKeys.append((t, (w, x, y, z)))
                self._check_semicolon()
            elif ktype in (1, 2):
                if self._read_int() != 3:
                    self._throw('Invalid vector key')
                v = self._read_vec3()
                (banim.posKeys if ktype == 2 else banim.scaleKeys).append((t, v))
            elif ktype in (3, 4):
                if self._read_int() != 16:
                    self._throw('Invalid matrix key')
                m = tuple(self._read_float() for _ in range(16))
                banim.trafoKeys.append((t, m))
                self._check_semicolon()
            else:
                self._throw('Unknown key type %d' % ktype)
            self._check_separator()
        self._check_closing_brace()

    def _parse_texture_filename(self):
        self._read_head()
        raw = self._next_token_as_string()
        self._check_closing_brace()
        s = raw.decode('utf-8', errors='replace') if isinstance(raw, bytes) else str(raw or '')
        while '\\\\' in s:
            s = s.replace('\\\\', '\\')
        return s

    def _parse_skin_weights(self, mesh):
        self._read_head()
        raw_name = self._next_token_as_string()
        bone = Bone()
        bone.name = raw_name.decode('utf-8', errors='replace') if isinstance(raw_name, bytes) else str(raw_name or '')
        mesh.bones.append(bone)
        n = self._read_int()
        for _ in range(n):
            bw = BoneWeight()
            bw.vertex = self._read_int()
            bone.weights.append(bw)
        for i in range(n):
            bone.weights[i].weight = self._read_float()
        bone.offsetMatrix = tuple(self._read_float() for _ in range(16))
        self._check_semicolon()
        self._check_closing_brace()

    def _parse_skin_header(self, mesh):
        self._read_head()
        self._read_int(); self._read_int(); self._read_int()
        self._check_closing_brace()

    def _skip_unknown(self):
        while True:
            t = self._next_token()
            if not t:
                self._throw('Unexpected EOF while skipping')
            if t == b'{':
                break
        depth = 1
        while depth > 0:
            t = self._next_token()
            if not t:
                self._throw('Unexpected EOF while skipping')
            if t == b'{':
                depth += 1
            elif t == b'}':
                depth -= 1

    def _find_next_non_ws(self):
        if self.isBinaryFormat:
            return
        while self.p < self.end:
            c = self.buffer[self.p:self.p + 1]
            if c in (b' ', b'\r', b'\n', b'\t'):
                if c == b'\n':
                    self.lineNumber += 1
                self.p += 1
                continue
            if self.buffer[self.p:self.p + 2] == b'//' or c == b'#':
                self._read_until_eol()
                continue
            break

    def _next_token(self):
        if self.isBinaryFormat:
            return self._next_bin_token()
        self._find_next_non_ws()
        if self.p >= self.end:
            return b''
        s = b''
        while self.p < self.end:
            c = self.buffer[self.p:self.p + 1]
            if c in (b' ', b'\t', b'\r', b'\n'):
                break
            if c in (b';', b'}', b'{', b','):
                if not s:
                    s = c
                    self.p += 1
                break
            s += c
            self.p += 1
        return s

    def _next_bin_token(self):
        if self.end - self.p < 2:
            return b''
        tok = self._read_bin_word()
        if tok == 1:
            if self.end - self.p < 4:
                return b''
            n = self._read_bin_dword()
            if n < 0 or self.p + n > self.end:
                return b''
            s = self.buffer[self.p:self.p + n]
            self.p += n
            return s
        elif tok == 2:
            if self.end - self.p < 4:
                return b''
            n = self._read_bin_dword()
            if self.p + n + 2 > self.end:
                return b''
            s = self.buffer[self.p:self.p + n]
            self.p += n + 2
            return s
        elif tok == 3:
            self.p += 4
            return b'<integer>'
        elif tok == 5:
            self.p += 16
            return b'<guid>'
        elif tok == 6:
            if self.end - self.p < 4:
                return b''
            n = self._read_bin_dword()
            self.p += n * 4
            return b'<int_list>'
        elif tok == 7:
            if self.end - self.p < 4:
                return b''
            n = self._read_bin_dword()
            self.p += n * (self.binaryFloatSize // 8)
            return b'<flt_list>'
        elif tok == 0x0a: return b'{'
        elif tok == 0x0b: return b'}'
        elif tok == 0x0c: return b'('
        elif tok == 0x0d: return b')'
        elif tok == 0x0e: return b'['
        elif tok == 0x0f: return b']'
        elif tok == 0x10: return b'<'
        elif tok == 0x11: return b'>'
        elif tok == 0x12: return b'.'
        elif tok == 0x13: return b','
        elif tok == 0x14: return b';'
        elif tok == 0x1f: return b'template'
        elif tok == 0x28: return b'WORD'
        elif tok == 0x29: return b'DWORD'
        elif tok == 0x2a: return b'FLOAT'
        elif tok == 0x2b: return b'DOUBLE'
        elif tok == 0x2c: return b'CHAR'
        elif tok == 0x2d: return b'UCHAR'
        elif tok == 0x2e: return b'SWORD'
        elif tok == 0x2f: return b'SDWORD'
        elif tok == 0x30: return b'void'
        elif tok == 0x31: return b'string'
        elif tok == 0x32: return b'unicode'
        elif tok == 0x33: return b'cstring'
        elif tok == 0x34: return b'array'
        else:
            self._throw('Unknown binary token 0x%02x' % tok)
            return b''

    def _read_head(self):
        t = self._next_token()
        if t != b'{':
            if self._next_token() != b'{':
                self._throw('Opening brace expected.')
            return t
        return b''

    def _check_closing_brace(self):
        if self._next_token() != b'}':
            self._throw('Closing brace expected.')

    def _check_semicolon(self):
        if self.isBinaryFormat:
            return
        if self._next_token() != b';':
            self._throw('Semicolon expected.')

    def _check_separator(self):
        if self.isBinaryFormat:
            return
        if self._next_token() not in (b',', b';'):
            self._throw("Separator expected.")

    def _test_separator(self):
        if self.isBinaryFormat:
            return
        self._find_next_non_ws()
        if self.p < self.end and self.buffer[self.p] in (59, 44):
            self.p += 1

    def _next_token_as_string(self):
        if self.isBinaryFormat:
            return self._next_token()
        self._find_next_non_ws()
        if self.p >= self.end:
            self._throw('Unexpected EOF while parsing string')
        if self.buffer[self.p:self.p + 1] != b'"':
            self._throw('Expected quotation mark.')
        self.p += 1
        buf = bytearray()
        while self.p < self.end and self.buffer[self.p:self.p + 1] != b'"':
            buf.append(self.buffer[self.p])
            self.p += 1
        if self.p >= self.end:
            self._throw('Unexpected EOF while parsing string')
        self.p += 1
        if self.p < self.end and self.buffer[self.p:self.p + 1] == b';':
            self.p += 1
        return bytes(buf)

    def _read_until_eol(self):
        if self.isBinaryFormat:
            return
        while self.p < self.end:
            c = self.buffer[self.p:self.p + 1]
            if c in (b'\n', b'\r'):
                self.p += 1
                self.lineNumber += 1
                return
            self.p += 1

    def _read_bin_word(self):
        v = struct.unpack_from('H', self.buffer, self.p)[0]
        self.p += 2
        return v

    def _read_bin_dword(self):
        v = struct.unpack_from('I', self.buffer, self.p)[0]
        self.p += 4
        return v

    def _read_int(self):
        if self.isBinaryFormat:
            if self.binaryNumCount == 0 and self.end - self.p >= 2:
                tmp = self._read_bin_word()
                if tmp == 0x06 and self.end - self.p >= 4:
                    self.binaryNumCount = self._read_bin_dword()
                else:
                    self.binaryNumCount = 1
            self.binaryNumCount -= 1
            if self.end - self.p >= 4:
                return self._read_bin_dword()
            self.p = self.end
            return 0
        self._find_next_non_ws()
        neg = False
        if self.p < self.end and self.buffer[self.p:self.p + 1] == b'-':
            neg = True
            self.p += 1
        start = self.p
        if start >= self.end or not self.buffer[start:start + 1].isdigit():
            self._throw('Number expected.')
        while self.p < self.end and self.buffer[self.p:self.p + 1].isdigit():
            self.p += 1
        num = int(self.buffer[start:self.p])
        self._check_separator()
        return -num if neg else num

    def _read_float(self):
        if self.isBinaryFormat:
            if self.binaryNumCount == 0 and self.end - self.p >= 2:
                tmp = self._read_bin_word()
                if tmp == 0x07 and self.end - self.p >= 4:
                    self.binaryNumCount = self._read_bin_dword()
                else:
                    self.binaryNumCount = 1
            self.binaryNumCount -= 1
            if self.binaryFloatSize == 64:
                if self.end - self.p >= 8:
                    v = struct.unpack_from('d', self.buffer, self.p)[0]
                    self.p += 8
                    return v
                self.p = self.end
                return 0.0
            else:
                if self.end - self.p >= 4:
                    v = struct.unpack_from('f', self.buffer, self.p)[0]
                    self.p += 4
                    return v
                self.p = self.end
                return 0.0
        self._find_next_non_ws()
        if self.p >= self.end:
            self._throw('Unexpected EOF while parsing float')
        for sp in (b'-1.#IND00', b'1.#IND00', b'1.#QNAN0'):
            n = len(sp)
            if self.buffer[self.p:self.p + n] == sp:
                self.p += n
                self._check_separator()
                return 0.0
        allowed = set(b'0123456789+-.eE')
        start = self.p
        while self.p < self.end and self.buffer[self.p] in allowed:
            self.p += 1
        if start == self.p:
            self._throw('Float expected.')
        try:
            v = float(self.buffer[start:self.p])
        except ValueError:
            self._throw('Invalid float: %r' % self.buffer[start:self.p])
        self._check_separator()
        return v

    def _read_vec2(self):
        x = self._read_float(); y = self._read_float()
        self._test_separator()
        return (x, y)

    def _read_vec3(self):
        x = self._read_float(); y = self._read_float(); z = self._read_float()
        self._test_separator()
        return (x, y, z)

    def _read_rgb(self):
        r = self._read_float(); g = self._read_float(); b = self._read_float()
        self._test_separator()
        return (r, g, b)

    def _read_rgba(self):
        r = self._read_float(); g = self._read_float()
        b = self._read_float(); a = self._read_float()
        self._test_separator()
        return (r, g, b, a)

    def _throw(self, text):
        if self.isBinaryFormat:
            raise ImportError('[binary @ %d] %s' % (self.p, text))
        raise ImportError('[line %d] %s' % (self.lineNumber, text))


def load_xfile_bytes(buffer):
    return XFileParser(buffer).scene

# ===========================================================================
# Section 1.5: MudRunner mixed-format XML header + material parsing
# ===========================================================================

def _scan_xml_block(data):
    """从 data 开头找第一段 XML 块，返回 (xml_text, end_offset) 或 (None, 0)。"""
    n = len(data)
    i = 0
    while i < n and data[i:i + 1] != b'<':
        i += 1
    if i >= n:
        return None, 0
    start = i
    # 跳过 XML 声明 <?xml ... ?>
    if data[i:i + 5] == b'<?xml':
        j = data.find(b'?>', i)
        if j < 0:
            return None, 0
        start = j + 2
        while start < n and data[start:start + 1] in b' \r\n\t':
            start += 1
    m = re.match(rb'<([A-Za-z_][\w:.-]*)', data[start:])
    if not m:
        return None, 0
    root = m.group(1)
    close = b'</' + root + b'>'
    end = data.find(close, start)
    if end >= 0:
        end += len(close)
        return data[start:end].decode('utf-8', errors='replace'), end
    # 自闭合根节点
    self_close = re.search(rb'<(?:[^>"\']|"[^"]*"|\'[^\']*\')*/>',
                           data[start:])
    if self_close:
        e = start + self_close.end()
        return data[start:e].decode('utf-8', errors='replace'), e
    return None, 0


def _extract_embedded_xml(filepath, max_scan=4 * 1024 * 1024):
    """尝试从文件开头提取内嵌 XML 头（MudRunner 混合格式）。

    返回 (xml_string_or_None, bytes_consumed_after_xml)。
      - 标准 DirectX X 文件（xof 开头）→ (None, 0)
      - SnowRunner 风格 [int32 len][xml bytes] → (xml, offset)
      - 直接以 XML 开头 → 匹配根标签提取
    """
    try:
        with open(filepath, 'rb') as f:
            head = f.read(4)
            if head == b'xof ':
                return None, 0
            f.seek(0)
            buf = f.read(4)
            if len(buf) == 4:
                try:
                    n = struct.unpack('<i', buf)[0]
                except Exception:
                    n = 0
                if 2 < n < 10 * 1024 * 1024:
                    f.seek(0)
                    raw = f.read(4 + (n - 2))
                    if len(raw) == 4 + (n - 2):
                        xml_bytes = raw[4:]
                        try:
                            xml = xml_bytes.decode('cp1251', errors='replace')
                        except Exception:
                            xml = xml_bytes.decode('utf-8', errors='replace')
                        if '<' in xml[:128]:
                            return xml, 4 + (n - 2) + 2
            f.seek(0)
            data = f.read(max_scan)
        return _scan_xml_block(data)
    except Exception:
        return None, 0


def parse_xml_materials(xml):
    """从 XML 中提取材质定义，以 MeshParts 网格名为索引。"""
    result = {}
    if not xml:
        return result
        
    mat_index = 0
    # 匹配 <Material ... /> 或 <Material ...>
    for m in re.finditer(r'<Material\b([^>]*?)/?>', xml, re.S):
        attrs_text = m.group(1) or ''
        attrs = dict(re.findall(r'(\w+)\s*=\s*"([^"]*)"', attrs_text))
        
        # 如果没有贴图属性，跳过
        if not any(k in attrs for k in ('DiffuseMap', 'AlbedoMap', 'NormalMap')):
            continue
            
        mesh_parts = attrs.get('MeshParts', '')
        
        # 【新增】生成一个共享材质名
        if 'Name' in attrs:
            mat_name = attrs['Name']
        elif mesh_parts:
            # 用第一个 mesh 的名字 + "_mat"，比如 "trak_001_mat"
            first_part = mesh_parts.split(',')[0].strip()
            mat_name = f"{first_part}_mat"
        else:
            mat_name = f"xml_material_{mat_index}"
            
        attrs['_MaterialName'] = mat_name
        mat_index += 1

        if mesh_parts:
            # 按逗号拆分，映射到每一个具体的网格名上
            for part in mesh_parts.split(','):
                part = part.strip()
                if part:
                    # 存全名（如 "Most 0"）
                    result[part] = dict(attrs)
                    # 如果有空格，把前面的词也存一份（如 "Most"），防止名字对不上
                    base_part = part.split()[0] if ' ' in part else part
                    result[base_part] = dict(attrs)
        else:
            # 兜底：没有 MeshParts 的按 Name 存
            name = attrs.get('Name') or attrs.get('TargetMaterialName')
            if name:
                result[name] = dict(attrs)
                
    return result

def parse_xml_socketpoints(xml):
    """从 XML 提取 <SocketPoints><SocketPoint Name="..." Pos="x,y,z" .../></SocketPoints>。"""
    result = []
    if not xml: return result
    m = re.search(r'<SocketPoints>(.*?)</SocketPoints>', xml, re.S)
    if not m: return result
    body = m.group(1)
    for sp in re.finditer(r'<SocketPoint\b([^>]*?)/?>', body, re.S):
        attrs = dict(re.findall(r'(\w+)\s*=\s*"([^"]*)"', sp.group(1)))
        name = attrs.get('Name') or attrs.get('name')
        pos = attrs.get('Pos') or attrs.get('pos') or '0,0,0'
        if name:
            result.append({'name': name, 'pos': pos})
    return result


def _parse_socket_pos(pos_str):
    """解析 XML 的 Pos 字符串，支持多种格式：
    - "1.5, 2.3, 0.0"
    - "1.5 2.3 0.0"
    - "(1.5, 2.3, 0.0)" / "[1.5, 2.3, 0.0]"
    - "1.5;2.3;0.0"
    """
    if pos_str is None:
        return None
    s = str(pos_str).strip()
    if not s:
        return None
    while s and s[0] in '([{':
        s = s[1:]
    while s and s[-1] in ')]}':
        s = s[:-1]
    s = s.strip()
    if not s:
        return None
    for sep in (',', ';'):
        if sep in s:
            parts = [p.strip() for p in s.split(sep) if p.strip()]
            if len(parts) >= 3:
                try:
                    return [float(parts[0]), float(parts[1]), float(parts[2])]
                except ValueError:
                    continue
    parts = s.split()
    if len(parts) >= 3:
        try:
            return [float(parts[0]), float(parts[1]), float(parts[2])]
        except ValueError:
            pass
    return None


def create_socket_locators(socket_points, parent=None, flip_axis='Z'):
    """按 XML 中的 Pos 创建 locator。返回实际创建成功的 locator 列表。"""
    created = []
    failed = 0
    for sp in socket_points:
        name_raw = sp.get('name', '?')
        pos_raw = sp.get('pos', '?')

        xyz = _parse_socket_pos(pos_raw)
        if xyz is None:
            failed += 1
            print("[xfile_importer] socket %r: cannot parse Pos=%r"
                  % (name_raw, pos_raw))
            continue
        x, y, z = xyz

        if flip_axis == 'Z':
            z = -z
        elif flip_axis == 'X':
            x = -x

        safe = ''.join(c if (c.isalnum() or c == '_') else '_'
                       for c in (name_raw or 'socket'))
        safe = safe or 'socket'

        try:
            loc = cmds.spaceLocator(name=safe)[0]
            cmds.xform(loc, translation=(x, y, z), worldSpace=True)
            if parent:
                try:
                    cmds.parent(loc, parent)
                except Exception as e:
                    print("[xfile_importer] socket %r: parent failed: %r"
                          % (name_raw, e))
            created.append(loc)
            print("[xfile_importer] socket %r created at (%.3f, %.3f, %.3f)"
                  % (name_raw, x, y, z))
        except Exception as e:
            failed += 1
            print("[xfile_importer] socket %r: spaceLocator failed: %r"
                  % (name_raw, e))

    print("[xfile_importer] create_socket_locators: %d created, %d failed"
          % (len(created), failed))
    return created


# ===========================================================================
# 骨骼-mesh 绑定关系查看
# ===========================================================================
def collect_bone_bindings(scene):
    """遍历 scene，收集所有 mesh 声明的骨骼绑定关系。

    返回 (bone_to_meshes, mesh_to_bones)：
      bone_to_meshes[bone_name] = [
          {'mesh': mesh_full, 'vertices': n_vtx, 'total_weight': w_sum}, ...
      ]
      mesh_to_bones[mesh_full] = [
          {'bone': bone_name, 'vertices': n_vtx, 'total_weight': w_sum}, ...
      ]

    注意：只依赖 X 文件里的 SkinWeights 数据，不依赖骨骼是否被建成 Maya 节点。
    即便某根骨骼没有对应 Frame，也能列出来（可用来发现 dangling reference）。
    """
    bone_to_meshes = defaultdict(list)
    mesh_to_bones = defaultdict(list)

    def _register(mesh_full, mesh):
        for bone in mesh.bones:
            if not bone.name:
                continue
            n_vtx = len(bone.weights)
            total_w = float(sum(bw.weight for bw in bone.weights))
            entry = {
                'mesh': mesh_full,
                'bone': bone.name,
                'vertices': n_vtx,
                'total_weight': total_w,
            }
            bone_to_meshes[bone.name].append(entry)
            mesh_to_bones[mesh_full].append(entry)

    def visit(node, path_prefix):
        if node is None:
            return
        node_path = (path_prefix + '|' + node.name
                     if path_prefix and node.name else (node.name or path_prefix))
        for idx, mesh in enumerate(node.meshes):
            base_hint = node.name or 'mesh'
            hint = ('%s_mesh%d' % (base_hint, idx + 1)
                    if len(node.meshes) > 1 else '%s_mesh' % base_hint)
            mesh_full = (node_path + '|' + hint) if node_path else hint
            _register(mesh_full, mesh)
        for c in node.children:
            visit(c, node_path)

    visit(scene.rootNode, '')
    for idx, mesh in enumerate(scene.globalMeshes):
        _register('globalMesh%d' % idx, mesh)

    return dict(bone_to_meshes), dict(mesh_to_bones)


def format_bone_bindings(scene, title=''):
    """把骨骼绑定关系格式化为可读文本（双向）。"""
    bone_to_meshes, mesh_to_bones = collect_bone_bindings(scene)
    if not bone_to_meshes and not mesh_to_bones:
        return '(该 X 文件没有任何 SkinWeights 数据)'

    lines = []
    if title:
        lines.append('=== %s ===' % title)
        lines.append('')

    # ── 骨骼 → 网格 ──
    lines.append('[ 骨骼 → 网格  (%d 根骨骼) ]' % len(bone_to_meshes))
    for bone_name in sorted(bone_to_meshes.keys()):
        entries = bone_to_meshes[bone_name]
        lines.append('  %s  (绑定 %d 个 mesh):' % (bone_name, len(entries)))
        for e in entries:
            lines.append('    - %s   verts=%d   weight_sum=%.3f'
                         % (e['mesh'], e['vertices'], e['total_weight']))
    lines.append('')

    # ── 网格 → 骨骼 ──
    lines.append('[ 网格 → 骨骼  (%d 个 mesh) ]' % len(mesh_to_bones))
    for mesh_name in sorted(mesh_to_bones.keys()):
        entries = mesh_to_bones[mesh_name]
        lines.append('  %s  (受 %d 根骨骼影响):'
                     % (mesh_name, len(entries)))
        for e in entries:
            lines.append('    - %s   verts=%d   weight_sum=%.3f'
                         % (e['bone'], e['vertices'], e['total_weight']))

    return '\n'.join(lines)


# ===========================================================================
# Section 2: Scene builder
# ===========================================================================

# Section 2 顶部
# 【优化】_TEX_INDEX_CACHE 的 key 变为 (root_dir, max_depth)，
# 兼容 _find_texture 各分段不同的 os.walk 深度
_TEX_INDEX_CACHE = {}    # (dir, max_depth) -> {lower_basename: full_path}
_TEX_MISS_WARNINGS = set()

def _build_tex_index(root_dir, max_depth=8):
    """一次性列出目录树里所有文件名（小写 -> 路径）。

    max_depth 用于精确对应原 _find_texture 各分段的 os.walk 深度：
      - extra_dirs（用户指定贴图目录）: 6
      - media_textures: 8
      - base_path（.x 所在目录）: 5
      - base_path 的父目录（跳过 base_path 子树）: 3
    """
    key = (root_dir, max_depth)
    if key in _TEX_INDEX_CACHE:
        return _TEX_INDEX_CACHE[key]
    idx = {}
    if os.path.isdir(root_dir):
        for r, dirs, files in os.walk(root_dir):
            depth = r[len(root_dir):].count(os.sep)
            if depth > max_depth:
                dirs[:] = []
                continue
            for f in files:
                idx.setdefault(f.lower(), os.path.join(r, f))
    _TEX_INDEX_CACHE[key] = idx
    return idx


# ===========================================================================
# Fallback colors (对齐 SnowRunner: name-hash → HSV → RGB)
# ===========================================================================

def _hsv_to_rgb(h, s, v):
    if s <= 0.0:
        return (v, v, v)
    h = h % 1.0
    i = int(h * 6.0)
    f = h * 6.0 - i
    p = v * (1.0 - s)
    q = v * (1.0 - s * f)
    t = v * (1.0 - s * (1.0 - f))
    i %= 6
    if i == 0: return (v, t, p)
    if i == 1: return (q, v, p)
    if i == 2: return (p, v, t)
    if i == 3: return (p, q, v)
    if i == 4: return (t, p, v)
    return (v, p, q)


def _color_for_name(name, index=0):
    """根据材质名生成稳定的可区分颜色。

    与 snowrunner_importer._color_for_name 完全一致：
      - 名字 hash 决定基础色相
      - index 做二次扰动（同一 mesh 内多个材质用不同 index 避免撞色）
      - 饱和度 0.85 / 亮度 0.95：颜色足够鲜艳，在视口里清晰可见
    """
    h = 0
    for ch in (name or ""):
        h = (h * 131 + ord(ch)) & 0xFFFFFFFF
    hue = ((h % 360) / 360.0 + index * 0.137) % 1.0
    return _hsv_to_rgb(hue, 0.85, 0.95)


def _convert_point(p, flip_axis):
    x, y, z = p
    if flip_axis == 'Z':
        return (x, y, -z)
    if flip_axis == 'X':
        return (-x, y, z)
    return (x, y, z)


def _convert_normal(n, flip_axis):
    return _convert_point(n, flip_axis)


def _x_matrix_to_maya(x_vals, flip_axis):
    M = [[float(x_vals[r * 4 + c]) for c in range(4)] for r in range(4)]
    if flip_axis == 'Z':
        for c in range(4): M[2][c] = -M[2][c]
        for r in range(4): M[r][2] = -M[r][2]
    elif flip_axis == 'X':
        for c in range(4): M[0][c] = -M[0][c]
        for r in range(4): M[r][0] = -M[r][0]
    return om.MMatrix([M[r][c] for r in range(4) for c in range(4)])


def _x_quat_to_maya_euler(q, flip_axis):
    w, x, y, z = q
    r00 = 1-2*(y*y+z*z); r01 = 2*(x*y+z*w); r02 = 2*(x*z-y*w)
    r10 = 2*(x*y-z*w);   r11 = 1-2*(x*x+z*z); r12 = 2*(y*z+x*w)
    r20 = 2*(x*z+y*w);   r21 = 2*(y*z-x*w);   r22 = 1-2*(x*x+y*y)
    M = [[r00, r01, r02, 0], [r10, r11, r12, 0],
         [r20, r21, r22, 0], [0, 0, 0, 1]]
    if flip_axis == 'Z':
        for c in range(4): M[2][c] = -M[2][c]
        for r in range(4): M[r][2] = -M[r][2]
    elif flip_axis == 'X':
        for c in range(4): M[0][c] = -M[0][c]
        for r in range(4): M[r][0] = -M[r][0]
    mm = om.MMatrix([M[r][c] for r in range(4) for c in range(4)])
    return om.MTransformationMatrix(mm).rotation()


def _sanitize_name(name, prefix='node', limit=60):
    """把名字清洗成 Maya 可接受的形态。
    Maya 允许字母、数字、下划线；其他字符统一替换为下划线。
    纯合法的名字（如 BoneRama_cdt、antena）不会被改变。
    """
    if not name:
        return prefix
    s = ''.join(c if (c.isalnum() or c == '_') else '_' for c in name)
    s = s.strip('_') or prefix
    return s[:limit]


def _collect_bone_names(scene):
    """收集所有 mesh.bones 里声明的骨骼名（含全局 mesh）。"""
    names = set()

    def visit(node):
        if node is None:
            return
        for mesh in node.meshes:
            for bone in mesh.bones:
                if bone.name:
                    names.add(bone.name)
        for c in node.children:
            visit(c)

    visit(scene.rootNode)
    for mesh in scene.globalMeshes:
        for bone in mesh.bones:
            if bone.name:
                names.add(bone.name)
    return names


def _pick_name(result):
    if result is None:
        return None
    if isinstance(result, (list, tuple)):
        for item in result:
            if item:
                return str(item)
        return None
    s = str(result).strip()
    return s if s else None


def _resolve_path(name):
    """返回场景中唯一的长路径；找不到时返回 None。"""
    name = _pick_name(name)
    if not name:
        return None
    s = str(name).strip()
    if not s or s in ('None', 'none', 'null', 'NULL', '0'):
        return None
    if cmds.objExists(s):
        if s.startswith('|'):
            return s
        matches = cmds.ls(s, long=True)
        if matches:
            return matches[-1]
        return s
    short = s.rsplit('|', 1)[-1]
    if not short or short in ('None', 'none'):
        return None
    matches = cmds.ls(short, long=True)
    if matches:
        return matches[-1]
    return None


def _unique_node_name(base):
    base = _sanitize_name(base, prefix='node')
    if not cmds.objExists(base):
        return base
    i = 1
    while cmds.objExists('%s_%d' % (base, i)):
        i += 1
    return '%s_%d' % (base, i)


# ===========================================================================
# 骨骼同名冲突消解：优先选与 mesh 同父的 joint，否则取第一个
# （无蒙皮版本：函数保留定义，不再调用）
# ===========================================================================
def _resolve_bone_joint(bone_name, mesh_name, bone_name_to_joints):
    """优先选与 mesh 同父的 joint；否则取第一个。"""
    cands = bone_name_to_joints.get(bone_name) or []
    if not cands:
        return None
    mesh_parent = cmds.listRelatives(mesh_name, parent=True, fullPath=True)
    mesh_parent = mesh_parent[0] if mesh_parent else ''
    for c in cands:
        if c.startswith(mesh_parent + '|'):
            return c
    return cands[0]


def _set_custom_normals(mesh_fn, mesh_data, flip_axis):
    """优先让 Maya 自动算法线（解决 X 文件法线导致的硬边黑斑）。
    如果 _IMPORT_CUSTOM_NORMALS 为 True，则尝试写入 X 文件的法线。
    """
    # 【关键】默认关闭，直接返回，让 Maya 自动算法线（等同于 1.3.0 报错后的效果）
    if not _IMPORT_CUSTOM_NORMALS:
        return

    if not mesh_data.normals or not mesh_data.normalFaces:
        return

    try:
        mesh_label = mesh_fn.partialPathName()
    except Exception:
        mesh_label = "<mesh>"

    same_layout = (len(mesh_data.normals) == len(mesh_data.positions)
                   and len(mesh_data.normalFaces) == len(mesh_data.posFaces))
    if same_layout:
        for pf, nf in zip(mesh_data.posFaces, mesh_data.normalFaces):
            if pf.indices != nf.indices:
                same_layout = False
                break

    # 路径 A：全顶点批量
    if same_layout:
        arr = om.MFloatVectorArray()
        for n in mesh_data.normals:
            nx, ny, nz = _convert_normal(n, flip_axis)
            arr.append(om.MFloatVector(float(nx), float(ny), float(nz)))

        # 方案 1：setNormals
        try:
            mesh_fn.setNormals(arr, om.MSpace.kObject)
            return
        except Exception as e1:
            _vprint("[xfile_importer] setNormals failed on %s: %r; "
                    "trying setVertexNormals" % (mesh_label, e1))

        # 方案 2：setVertexNormals
        try:
            mesh_fn.setVertexNormals(arr, om.MSpace.kObject)
            return
        except Exception as e2:
            print("[xfile_importer] setVertexNormals failed on %s: %r; "
                  "Maya will auto-compute normals" % (mesh_label, e2))
            return

    # 路径 B：面角批量:布局不一致 → 逐 face-vertex 设（face_ids 在前 vertex_ids 在后）
    arr = om.MFloatVectorArray()
    vertex_ids = om.MIntArray()
    face_ids = om.MIntArray()
    for fi, (pf, nf) in enumerate(zip(mesh_data.posFaces, mesh_data.normalFaces)):
        if len(pf.indices) != len(nf.indices):
            continue
        for j, nidx in enumerate(nf.indices):
            if 0 <= nidx < len(mesh_data.normals):
                nx, ny, nz = _convert_normal(mesh_data.normals[nidx], flip_axis)
                arr.append(om.MFloatVector(float(nx), float(ny), float(nz)))
                vertex_ids.append(j)
                face_ids.append(fi)

    if len(arr) == 0:
        return

    try:
        mesh_fn.setFaceVertexNormals(
            arr, face_ids, vertex_ids, om.MSpace.kObject)
    except Exception as e:
        print("[xfile_importer] setFaceVertexNormals failed on %s: %r; "
              "Maya will auto-compute normals" % (mesh_label, e))


def _apply_uvs_to_mesh(mesh_long, faces, uv_layers, flip_v):
    """
    在蒙皮前，用 API 2.0 的 MFnMesh.setUVs() + assignUVs() 写入面角 UV。

    对齐 snowrunner_importer.py 的实现：
      - XFile 的 texCoords 按顶点索引（每顶点一个 UV，无接缝数据），
        与 CombineXMesh 的 UV 语义一致。
      - 用 setUVs 写入唯一 UV 坐标池（长度 = 唯一 UV 数）。
      - 用 assignUVs 把 vert->uv_id 映射写入每个面角，正确处理 UV 接缝。
      - createUVSet 用 API，避免插入 createUVSet 历史节点。
      - 异常不静默吞掉，打印 traceback。
    """
    if not uv_layers:
        return
    try:
        shapes = cmds.listRelatives(mesh_long, shapes=True, fullPath=True) or []
        if not shapes:
            return
        shape_name = shapes[0]

        sel = om.MSelectionList()
        sel.add(shape_name)
        dag = sel.getDagPath(0)
        mesh_fn = om.MFnMesh(dag)

        for layer_idx, (uv_name, uv_data) in enumerate(uv_layers):
            if not uv_data:
                continue

            uv_set_name = "map1" if layer_idx == 0 else _sanitize_name(uv_name, prefix='uvSet')

            # 使用 API 创建 UV 集，避免插入 createUVSet 历史节点
            uv_sets = mesh_fn.getUVSetNames()
            if uv_set_name not in uv_sets:
                mesh_fn.createUVSet(uv_set_name)

            # 步骤 1：建立顶点索引 -> UV 索引映射（处理 UV 接缝）
            vert_to_uv = {}
            u_vals = []
            v_vals = []
            for face in faces:
                for vert_idx in face:
                    if vert_idx not in vert_to_uv:
                        if 0 <= vert_idx < len(uv_data):
                            u, v = uv_data[vert_idx]
                            vert_to_uv[vert_idx] = len(u_vals)
                            u_vals.append(float(u))
                            v_vals.append(1.0 - float(v) if flip_v else float(v))
                        else:
                            vert_to_uv[vert_idx] = len(u_vals)
                            u_vals.append(0.0)
                            v_vals.append(0.0)

            # 步骤 2：写入唯一 UV 坐标（长度 = 唯一 UV 数，不是面角数）
            u_array = om.MFloatArray(u_vals)
            v_array = om.MFloatArray(v_vals)
            mesh_fn.setUVs(u_array, v_array, uv_set_name)

            # 步骤 3：构造 assignUVs 参数（面数 + 面角 UV ID）
            face_counts = om.MIntArray()
            face_uv_ids = om.MIntArray()
            for face in faces:
                face_counts.append(len(face))
                for vert_idx in face:
                    face_uv_ids.append(vert_to_uv[vert_idx])

            # 步骤 4：分配 UV ID 到面角（这是真正把 UV 落到 mesh 上的关键一步）
            # ---- 先 bulk assignUVs ----
            bulk_ok = False
            try:
                mesh_fn.assignUVs(face_counts, face_uv_ids, uv_set_name)
                bulk_ok = True
            except RuntimeError as e:
                print("[xfile_importer] bulk assignUVs failed on %s: %r; "
                      "falling back to per-face bulk / per-face-vertex"
                      % (shape_name, e))

            # ---- 【优化】分两级 fallback ----
            # 先试 per-face bulk assignUVs（1 次 API 设 3~4 个 UV），
            # 只有失败的面才逐面角 assignUV
            if not bulk_ok:
                assigned = 0
                failed = 0
                n_face_ok = 0
                n_face_fail = 0
                for fi, face in enumerate(faces):
                    try:
                        fc = om.MIntArray([len(face)])
                        fuv = om.MIntArray([vert_to_uv[v] for v in face])
                        mesh_fn.assignUVs(fc, fuv, uv_set_name)
                        assigned += len(face)
                        n_face_ok += 1
                    except (RuntimeError, TypeError):
                        n_face_fail += 1
                        for j, vert_idx in enumerate(face):
                            uv_id = vert_to_uv[vert_idx]
                            try:
                                mesh_fn.assignUV(fi, j, uv_id, uv_set_name)
                                assigned += 1
                            except (RuntimeError, TypeError):
                                failed += 1
                print("[xfile_importer] assignUV fallback on %s: "
                      "%d face-vertex(s) assigned, %d failed "
                      "(per-face bulk ok=%d, fail=%d)"
                      % (shape_name, assigned, failed, n_face_ok, n_face_fail))

            _vprint("[xfile_importer] UV applied via API on %s: %d face(s), "
                  "%d uv(s), uvSet=%r"
                  % (shape_name, len(face_counts), len(u_vals), uv_set_name))

        #cmds.polyUVSet(shape_name, currentUVSet=True, uvSet="map1") #Maya 自动它就是当前 UV 集，不需要 polyUVSet 再设一次

    except Exception:
        traceback.print_exc()
        print("[xfile_importer] UV setup failed for %r" % mesh_long)


def _x_mat4_mul(a, b):
    """行向量语义：result = a · b"""
    return [[sum(a[i][k] * b[k][j] for k in range(4)) for j in range(4)]
            for i in range(4)]

def _x_apply_point(m, p):
    """行向量：p · m"""
    x = p[0]*m[0][0] + p[1]*m[1][0] + p[2]*m[2][0] + m[3][0]
    y = p[0]*m[0][1] + p[1]*m[1][1] + p[2]*m[2][1] + m[3][1]
    z = p[0]*m[0][2] + p[1]*m[1][2] + p[2]*m[2][2] + m[3][2]
    return (x, y, z)

def _x_identity4():
    return [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]

def _x_mat4_from_flat(vals):
    """X 行优先 16 元组 → 4x4 list-of-lists"""
    return [[float(vals[r * 4 + c]) for c in range(4)] for r in range(4)]


def _compute_mesh_bind_world(mesh_data, x_frames_world):
    """【无蒙皮版本】保留定义，不再调用。"""
    for bone in mesh_data.bones:
        if not bone.offsetMatrix or len(bone.offsetMatrix) != 16:
            continue
        if bone.name not in x_frames_world:
            continue
        bone_world = x_frames_world[bone.name]
        offset = _x_mat4_from_flat(bone.offsetMatrix)
        return _x_mat4_mul(bone_world, offset)
    return None

def _compute_vertex_bind_worlds(mesh_data, x_frames_world, node_x_world=None):
    """【无蒙皮版本】保留定义，不再调用。"""
    if not mesh_data.bones:
        return None

    bone_names_in_weights = [b.name for b in mesh_data.bones if b.weights]
    if len(bone_names_in_weights) <= 1:
        mbw = _compute_mesh_bind_world(mesh_data, x_frames_world)
        if mbw is None:
            return None
        return [_x_apply_point(mbw, p) for p in mesh_data.positions]

    n = len(mesh_data.positions)
    vert_transforms = [[] for _ in range(n)]
    any_matched = False

    for bone in mesh_data.bones:
        if not bone.offsetMatrix or len(bone.offsetMatrix) != 16:
            continue
        if bone.name not in x_frames_world:
            continue
        any_matched = True
        M = _x_mat4_mul(x_frames_world[bone.name],
                        _x_mat4_from_flat(bone.offsetMatrix))
        for bw in bone.weights:
            if 0 <= bw.vertex < n and bw.weight > 0.0:
                vert_transforms[bw.vertex].append((M, float(bw.weight)))

    if not any_matched:
        return None

    result = []
    for i, p in enumerate(mesh_data.positions):
        ts = vert_transforms[i]
        total_w = sum(w for _, w in ts)
        if not ts or total_w <= 1e-9:
            result.append(_x_apply_point(node_x_world, p)
                          if node_x_world is not None else p)
            continue
        px = py = pz = 0.0
        for M, w in ts:
            tp = _x_apply_point(M, p)
            px += w * tp[0]; py += w * tp[1]; pz += w * tp[2]
        if abs(total_w - 1.0) > 1e-6:
            px /= total_w; py /= total_w; pz /= total_w
        result.append((px, py, pz))
    return result

def _create_mesh_shape(mesh_data, parent_name, flip_axis, flip_v,
                       name_hint=None, x_world=None, vertex_worlds=None):
    if not mesh_data.positions or not mesh_data.posFaces:
        print("[xfile_importer] skip mesh: no vertices or faces")
        return None

    n_verts = len(mesh_data.positions)

    pts = om.MPointArray()
    pts.setLength(n_verts)
    for i, p in enumerate(mesh_data.positions):
        if vertex_worlds is not None:
            p = vertex_worlds[i]
        elif x_world is not None:
            p = _x_apply_point(x_world, p)
        x, y, z = _convert_point(p, flip_axis)
        pts[i] = om.MPoint(float(x), float(y), float(z))

    poly_counts = om.MIntArray()
    poly_connects = om.MIntArray()
    valid_faces = []
    skipped = 0
    for face in mesh_data.posFaces:
        idxs = [int(i) for i in face.indices]
        if not idxs or any(i < 0 or i >= n_verts for i in idxs):
            skipped += 1
            continue
    # 任何 flip（Z/X/None）都是镜像或手性翻转，必须反转顶点顺序，
    # 否则法线朝内，光照 = 0 → 面显示黑色。
    # （flip_axis=None 表示不做坐标翻转，但 X 文件本身是左手系，
    #   导入 Maya 右手系也需要反转手性）
        if flip_axis in ('Z', 'X', None):
           idxs = list(reversed(idxs))
        poly_counts.append(len(idxs))
        for idx in idxs:
            poly_connects.append(idx)
        valid_faces.append(tuple(idxs))

    if len(poly_counts) == 0:
        print("[xfile_importer] skip mesh: no valid faces")
        return None

    try:
        mesh_fn = om.MFnMesh()
        transform_mobj = mesh_fn.create(pts, poly_counts, poly_connects)
    except Exception as e:
        print("[xfile_importer] MFnMesh.create failed: %r" % e)
        traceback.print_exc()
        return None

    if transform_mobj is None or transform_mobj.isNull():
        print("[xfile_importer] MFnMesh.create returned null MObject")
        return None

    try:
        dag_fn = om.MFnDagNode(transform_mobj)
        short_name = dag_fn.partialPathName()
    except Exception as e:
        print("[xfile_importer] cannot get name from new mesh: %r" % e)
        return None

    ls_res = cmds.ls(short_name, long=True) or []
    if not ls_res:
        print("[xfile_importer] mesh created but not registered as %r" % short_name)
        return None
    transform_name = ls_res[0]

    desired = _sanitize_name(name_hint or 'mesh', prefix='mesh')
    try:
        final_name = _unique_node_name(desired)
        renamed = cmds.rename(transform_name, final_name)
        ls2 = cmds.ls(renamed, long=True) or [renamed]
        transform_name = ls2[0]
    except Exception as e:
        print("[xfile_importer] rename mesh failed: %r" % e)

    parent_path = _resolve_path(parent_name)
    if parent_path:
        try:
            # 【Fix B】relative=True：mesh local matrix 保持 identity，
            # 世界坐标 = parent.world × 顶点局部，跟着 parent 变换走。
            res = cmds.parent(transform_name, parent_path, relative=True)
            res_name = _pick_name(res)
            if res_name:
                ls3 = cmds.ls(res_name, long=True) or [res_name]
                transform_name = ls3[0]
        except Exception as e:
            print("[xfile_importer] parent mesh failed: %r" % e)

    try:
        shapes = cmds.listRelatives(transform_name, shapes=True,
                                    fullPath=True) or []
        for s in shapes:
            try:
                cmds.setAttr(s + ".doubleSided", 1)
            except Exception as e:
                print("[xfile_importer] doubleSided failed on %s: %r" % (s, e))
    except Exception as e:
        print("[xfile_importer] listRelatives failed for %s: %r"
              % (transform_name, e))

    try:
        _set_custom_normals(mesh_fn, mesh_data, flip_axis)
    except Exception as e:
        print("[xfile_importer] normals failed: %r" % e)

    if mesh_data.texCoords:
        uv_layers = []
        for layer_idx, uv_data in enumerate(mesh_data.texCoords):
            uv_name = 'UVMap' if layer_idx == 0 else 'UVMap%d' % (layer_idx + 1)
            uv_layers.append((uv_name, uv_data))
        try:
            _apply_uvs_to_mesh(transform_name, valid_faces, uv_layers, flip_v)
        except Exception as e:
            print("[xfile_importer] uv apply failed: %r" % e)

    if skipped:
        print("[xfile_importer] mesh imported with %d face(s) skipped" % skipped)

    return transform_name


def _resolve_material(mat, global_materials):
    if not mat.isReference:
        return mat
    for g in global_materials:
        if g.name == mat.name and not g.isReference:
            return g
    return mat

def _find_media_textures(base_path):
    """如果 base_path 位于 'Media' 目录内或子文件夹内，返回该 Media 下的
    'textures' 目录路径（大小写不敏感），否则返回 None。

    例：base_path = F:/mod/.../Media/meshes/trucks
        → 向上找到 Media，返回 F:/mod/.../Media/textures
    """
    if not base_path:
        return None
    try:
        curr = os.path.abspath(base_path)
    except Exception:
        return None

    for _ in range(5):  # 最多向上找 8 层，防止无限循环
        if not curr or not os.path.isdir(curr):
            break
        if os.path.basename(curr).lower() == 'media':
            # 命中 Media，找它的 textures 子目录（大小写不敏感）
            try:
                for name in os.listdir(curr):
                    if name.lower() == 'textures':
                        tex_dir = os.path.join(curr, name)
                        if os.path.isdir(tex_dir):
                            return tex_dir
            except OSError:
                pass
            return None  # 找到了 Media 但没有 textures 子目录
        parent = os.path.dirname(curr)
        if parent == curr:
            break
        curr = parent
    return None

def _find_texture(base_path, tex_name, extra_dirs=None):
    # 【优化】用 _build_tex_index 一次性索引替代 os.walk 递归
    if not tex_name:
        return None
    tex_name = tex_name.replace('\\\\', '\\').replace('\\', '/')
    basename = os.path.basename(tex_name)
    if not basename:
        return None
    basename_lc = basename.lower()

    # 1. 优先在用户 UI 指定的 Textures folder 里找
    if extra_dirs:
        for d in extra_dirs:
            if not d or not os.path.isdir(d):
                continue
            direct = os.path.join(d, tex_name)
            if os.path.isfile(direct):
                return direct
            same = os.path.join(d, basename)
            if os.path.isfile(same):
                return same
            # 【优化】索引（深度 6，与原 os.walk 深度限制一致）
            hit = _build_tex_index(d, max_depth=6).get(basename_lc)
            if hit:
                return hit

    # 1.5. 【新增】从 base_path 向上最多 4 层，每层找同级 'textures' 子目录
    try:
        cur = os.path.abspath(base_path)
        for _ in range(4):
            if not cur or not os.path.isdir(cur):
                break
            for sub_name in ('textures', 'Textures', 'TEXTURES'):
                cand = os.path.join(cur, sub_name)
                if os.path.isdir(cand):
                    direct = os.path.join(cand, tex_name)
                    if os.path.isfile(direct):
                        return direct
                    same = os.path.join(cand, basename)
                    if os.path.isfile(same):
                        return same
                    hit = _build_tex_index(cand, max_depth=6).get(basename_lc)
                    if hit:
                        return hit
            parent = os.path.dirname(cur)
            if parent == cur:
                break
            cur = parent
    except Exception:
        pass

    # 2. 用户目录里没找到 → X 文件在 Media 内/子文件夹 → 去 Media\textures 找
    media_tex_dir = _find_media_textures(base_path)
    if media_tex_dir:
        direct = os.path.join(media_tex_dir, tex_name)
        if os.path.isfile(direct):
            return direct
        same = os.path.join(media_tex_dir, basename)
        if os.path.isfile(same):
            return same
        # 【优化】索引（深度 8）
        hit = _build_tex_index(media_tex_dir, max_depth=8).get(basename_lc)
        if hit:
            return hit

    # 3. 绝对路径直接返回
    if os.path.isabs(tex_name) and os.path.isfile(tex_name):
        return tex_name

    # 4. 在 base_path（.x 所在目录）及子目录找
    direct = os.path.join(base_path, tex_name)
    if os.path.isfile(direct):
        return direct
    same_dir = os.path.join(base_path, basename)
    if os.path.isfile(same_dir):
        return same_dir

    if os.path.isdir(base_path):
        # 【优化】索引（深度 5）
        hit = _build_tex_index(base_path, max_depth=5).get(basename_lc)
        if hit:
            return hit

    # 5. 在 base_path 的父目录（跳过 base_path 子树）找
    parent = os.path.dirname(os.path.abspath(base_path))
    if parent and os.path.isdir(parent) and parent != os.path.abspath(base_path):
        # 【优化】用索引（深度 3），但命中必须在 base_path 之外
        base_abs = os.path.abspath(base_path)
        parent_abs = os.path.abspath(parent)
        hit = _build_tex_index(parent_abs, max_depth=3).get(basename_lc)
        if hit and not os.path.abspath(hit).startswith(base_abs + os.sep):
            return hit

    return None


def _acquire_phong(name):
    safe = _sanitize_name(name, prefix='phong')
    if cmds.objExists(safe):
        if cmds.nodeType(safe) == 'phong':
            return safe
        safe = safe + '#'
    try:
        return cmds.shadingNode('phong', asShader=True, name=safe)
    except Exception:
        return cmds.shadingNode('phong', asShader=True, name=safe + '#')


def _ensure_shading_group(sg_name, shader):
    sgs = cmds.listConnections(shader + '.outColor',
                               source=False, destination=True,
                               type='shadingEngine') or []
    if sgs:
        sg = sgs[0]
        if sg != sg_name:
            try:
                renamed = cmds.rename(sg, sg_name)
                if renamed:
                    sg = renamed
            except Exception:
                pass
        return sg

    if cmds.objExists(sg_name):
        sg = sg_name
    else:
        sg = cmds.sets(renderable=True, noSurfaceShader=True, empty=True)
        try:
            renamed = cmds.rename(sg, sg_name)
            if renamed:
                sg = renamed
        except Exception:
            try:
                renamed = cmds.rename(sg, sg_name + '#')
                if renamed:
                    sg = renamed
            except Exception:
                pass
    try:
        cmds.connectAttr(shader + '.outColor', sg + '.surfaceShader',
                         force=True)
    except Exception as e:
        print("[xfile_importer] connectAttr failed %s -> %s: %r"
              % (shader, sg, e))
    return sg


def _acquire_file_node(shader, safe, tex_path):
    base_name = safe + '_file'
    if cmds.objExists(base_name):
        if cmds.nodeType(base_name) == 'file':
            try:
                cmds.setAttr(base_name + '.fileTextureName', tex_path,
                             type='string')
            except Exception:
                pass
            return base_name
    try:
        file_node = cmds.shadingNode('file', asTexture=True,
                                     name=base_name + '#')
    except Exception:
        file_node = cmds.shadingNode('file', asTexture=True)

    try:
        cmds.setAttr(file_node + '.fileTextureName', tex_path, type='string')
    except Exception as e:
        print("[xfile_importer] set fileTextureName failed: %r" % e)

    # 【关键】照 snowrunner 加 place2dTexture，否则 uvCoord 默认 (0,0)，
    # 整个 mesh 只采样一个 texel → 视觉上黑色/纯色
    try:
        p2d_name = safe + '_p2d'
        try:
            p2d = cmds.shadingNode('place2dTexture', asUtility=True,
                                   name=p2d_name + '#')
        except Exception:
            p2d = cmds.shadingNode('place2dTexture', asUtility=True)
        cmds.connectAttr(p2d + '.outUV', file_node + '.uvCoord', force=True)
        cmds.connectAttr(p2d + '.outUvFilterSize',
                         file_node + '.uvFilterSize', force=True)
    except Exception as e:
        print("[xfile_importer] place2dTexture setup failed: %r" % e)

    # 【可选】设 colorSpace（jpg/png 用 sRGB，normal map 用 Raw）
    try:
        cmds.setAttr(file_node + '.colorSpace', 'sRGB', type='string')
    except Exception:
        pass

    return file_node

def _create_material_node(mat, base_path, tex_dir=None):
    extra_tex = getattr(mat, 'xml_props', None) or {}
    albedo = extra_tex.get('AlbedoMap') or extra_tex.get('DiffuseMap')
    normal_map = extra_tex.get('NormalMap') or extra_tex.get('NormalmapMap')

    # 缓存 key 使用材质名 + 贴图名，确保相同配置的材质复用同一个节点
    cache_key = (mat.name or '', albedo or '', base_path, tex_dir or '')
    if cache_key in _XFILE_MATERIAL_CACHE:
        return _XFILE_MATERIAL_CACHE[cache_key]

    safe = _sanitize_name(mat.name, prefix='material')
    shader = _acquire_phong(safe)

    r, g, b = _color_for_name(mat.name or 'material')
    _vprint("[xfile_importer] fallback color for %r = (%.3f, %.3f, %.3f)"
          % (mat.name, r, g, b))

    try:
        cmds.setAttr(shader + '.color', r, g, b, type='double3')
        cmds.setAttr(shader + '.cosinePower',
                     max(2.0, float(mat.specularExponent)))
        cmds.setAttr(shader + '.specularColor',
                     mat.specular[0], mat.specular[1], mat.specular[2],
                     type='double3')
        alpha = mat.diffuse[3] if len(mat.diffuse) > 3 else 1.0
        if alpha < 1.0:
            cmds.setAttr(shader + '.transparency',
                         1.0 - alpha, 1.0 - alpha, 1.0 - alpha,
                         type='double3')
    except Exception as e:
        print("[xfile_importer] set phong attrs failed for %r: %r"
              % (safe, e))

    extra_dirs = [tex_dir] if tex_dir else None

    tex_candidates = []
    if albedo:
        tex_candidates.append(albedo)
    if mat.textures:
        for t in mat.textures:
            if t and t.name:
                tex_candidates.append(t.name)
                break
    for cand in tex_candidates:
        try:
            tex_path = _find_texture(base_path, cand, extra_dirs=extra_dirs)
            if tex_path:
                file_node = _acquire_file_node(shader, safe, tex_path)
                cmds.connectAttr(file_node + '.outColor',
                                 shader + '.color', force=True)
                                 
                # 【新增】处理透明/混合贴图
                blending = extra_tex.get('Blending', '').lower()
                if 'alpha' in blending:
                    # 如果贴图有 Alpha 通道，连到 phong 的透明度
                    cmds.connectAttr(file_node + '.outTransparency',
                                     shader + '.transparency', force=True)
                                     
                print("[xfile_importer] texture resolved: %s -> %s"
                      % (cand, tex_path))
                break
            else:
                if cand.lower() not in _TEX_MISS_WARNINGS:
                    _TEX_MISS_WARNINGS.add(cand.lower())
                    cmds.warning('Texture not found: %s' % cand)
        except Exception as e:
            print("[xfile_importer] texture setup failed for %r: %r"
                  % (safe, e))

    if normal_map:
        try:
            nm_path = _find_texture(base_path, normal_map,
                                    extra_dirs=extra_dirs)
            if nm_path:
                nm_file = _acquire_file_node(shader, safe + '_n', nm_path)
                try:
                    cmds.setAttr(nm_file + '.colorSpace', 'Raw', type='string')
                except Exception:
                    pass
                bump = cmds.shadingNode('bump2d', asUtility=True,
                                        name=safe + '_bump#')
                cmds.connectAttr(nm_file + '.outAlpha',
                                 bump + '.bumpValue', force=True)
                cmds.connectAttr(bump + '.outNormal',
                                 shader + '.normalCamera', force=True)
        except Exception as e:
            print("[xfile_importer] normal map failed for %r: %r"
                  % (safe, e))

    sg_node = _ensure_shading_group(safe + '_SG', shader)
    _XFILE_MATERIAL_CACHE[cache_key] = (shader, sg_node)
    return shader, sg_node


_COLLISION_MAT_NAME = "MudRunner_Collision"


def _create_collision_material():
    cache_key = ('__collision__', '', '')
    if cache_key in _XFILE_MATERIAL_CACHE:
        return _XFILE_MATERIAL_CACHE[cache_key]
    shader = _acquire_phong(_COLLISION_MAT_NAME)
    try:
        cmds.setAttr(shader + '.color', 1.0, 0.35, 0.05, type='double3')
        cmds.setAttr(shader + '.transparency', 0.5, 0.5, 0.5, type='double3')
        cmds.setAttr(shader + '.cosinePower', 5.0)
    except Exception:
        pass
    sg = _ensure_shading_group(_COLLISION_MAT_NAME + '_SG', shader)
    _XFILE_MATERIAL_CACHE[cache_key] = (shader, sg)
    return shader, sg


def _faces_to_component_string(mesh_name, face_indices):
    if not face_indices:
        return ""
    faces = sorted(set(face_indices))
    ranges = []
    start = prev = faces[0]
    for f in faces[1:]:
        if f == prev + 1:
            prev = f
        else:
            ranges.append((start, prev))
            start = prev = f
    ranges.append((start, prev))
    parts = []
    for s, e in ranges:
        if s == e:
            parts.append("%s.f[%d]" % (mesh_name, s))
        else:
            parts.append("%s.f[%d:%d]" % (mesh_name, s, e))
    return " ".join(parts)


def _assign_faces_to_sg(mesh_name, face_list, sg):
    if not face_list or not sg:
        return
    if not cmds.objExists(sg):
        print("[xfile_importer] shading group %r does not exist; skipping "
              "%d face(s) on %s" % (sg, len(face_list), mesh_name))
        return
    face_str = _faces_to_component_string(mesh_name, face_list)
    if not face_str:
        return
    try:
        cmds.sets(face_str, edit=True, forceElement=sg)
        return
    except Exception as e:
        print("[xfile_importer] sets(face_str) failed on %s: %r; "
              "falling back to per-face" % (mesh_name, e))
    for fi in face_list:
        try:
            cmds.sets("%s.f[%d]" % (mesh_name, fi),
                      edit=True, forceElement=sg)
        except Exception:
            pass


def _assign_materials(shape_path, face_materials, sg_list):
    if not face_materials or not sg_list:
        return
    groups = {}
    for fi, mi in enumerate(face_materials):
        if 0 <= mi < len(sg_list):
            groups.setdefault(mi, []).append(fi)
    for mi, faces in groups.items():
        _assign_faces_to_sg(shape_path, faces, sg_list[mi])


def _create_joint(name, parent_name):
    """用 cmds.createNode('joint') 创建 joint，然后用 relative=True 挂到父级。

    【关键】cmds.parent 对 joint 的默认行为是 absolute=True，会在 parent 有
    旋转时插入中间 transformN 来"保持世界位置不变"，导致 child.world = local
    （父级变换被抵消）。

    显式传 relative=True，让 local matrix 保持 identity（不被 Maya 调整），
    world = identity × parent.world。随后 _apply_matrix 设 local = trafoMatrix，
    最终 world = trafoMatrix × parent.world，符合 X 文件的 local matrix 语义。
    """
    unique = _unique_node_name(name or 'joint')
    try:
        raw = cmds.createNode('joint', name=unique)
    except RuntimeError:
        raw = cmds.createNode('joint')
    j = _pick_name(raw)
    if not j:
        return None

    if parent_name is not None:
        parent_path = _resolve_path(parent_name)
        if parent_path:
            try:
                # 【关键】显式 relative=True，让 Maya 不插中间层、不调整 jointOrient
                raw = cmds.parent(j, parent_path, relative=True)
                j = _pick_name(raw) or j
            except Exception as e:
                print("[xfile_importer] parent joint %s -> %s failed: %r"
                      % (j, parent_path, e))

    cmds.select(clear=True)
    return _resolve_path(j) or j


def _create_transform(name, parent_name):
    unique = _unique_node_name(name or 'group')
    try:
        raw = cmds.createNode('transform', name=unique)
    except RuntimeError:
        raw = cmds.createNode('transform')
    t = _pick_name(raw)
    if not t:
        return None

    if parent_name is not None:
        parent_path = _resolve_path(parent_name)
        if parent_path:
            try:
                # 显式 relative=True，保证 local matrix 保持 identity
                raw = cmds.parent(t, parent_path, relative=True)
                t = _pick_name(raw) or t
            except Exception as e:
                print("[xfile_importer] parent transform %s -> %s failed: %r"
                      % (t, parent_path, e))

    return _resolve_path(t) or t


def _apply_matrix(name, x_matrix, flip_axis):
    if not x_matrix or len(x_matrix) != 16:
        return
    path = _resolve_path(name)
    if path is None:
        return
    try:
        try:
            if cmds.nodeType(path) == 'joint':
                cmds.setAttr(path + '.jointOrient', 0, 0, 0, type='double3')
        except Exception:
            pass

        # x_matrix 是行优先 4x4：M[r][c] = x_matrix[r*4+c]，平移在 M[3][0..2]
        M = [[float(x_matrix[r * 4 + c]) for c in range(4)] for r in range(4)]

        # F · M · F
        if flip_axis == 'Z':
            for c in range(4): M[2][c] = -M[2][c]
            for r in range(4): M[r][2] = -M[r][2]
        elif flip_axis == 'X':
            for c in range(4): M[0][c] = -M[0][c]
            for r in range(4): M[r][0] = -M[r][0]

        # 【关键】cmds.xform(matrix=) 直接接受行优先 16 个 float。
        flat = [M[r][c] for r in range(4) for c in range(4)]
        cmds.xform(path, matrix=flat, worldSpace=False)
    except Exception as e:
        print("[xfile_importer] xform %s failed: %r" % (path, e))


def _bind_skin(mesh_name, joint_names_list, mesh_data, bone_name_to_joint,
               prefer_batch=False):
    """【无蒙皮版本】保留定义，不再调用。"""
    if not mesh_data.bones or not joint_names_list:
        return
    try:
        result = cmds.skinCluster(
            mesh_name, *joint_names_list,
            bindMethod=0, skinMethod=0, normalizeWeights=1,
            maximumInfluences=4, obeyMaxInfluences=True)
    except Exception as e:
        print("[xfile_importer] skinCluster failed: %r" % e)
        return

    skin = None
    for r in result:
        if cmds.nodeType(r) == 'skinCluster':
            skin = r
            break
    if skin is None:
        skin = result[0]

    if prefer_batch:
        try:
            _bind_skin_setweights(mesh_name, skin, joint_names_list,
                                  mesh_data, bone_name_to_joint)
            return
        except Exception as e:
            print("[xfile_importer] setWeights failed on %s: %r; "
                  "falling back to skinPercent" % (mesh_name, e))

    vert_weights = {}
    for bone in mesh_data.bones:
        jname = bone_name_to_joint.get(bone.name)
        if jname is None:
            continue
        for bw in bone.weights:
            vert_weights.setdefault(bw.vertex, {})[jname] = \
                vert_weights.get(bw.vertex, {}).get(jname, 0.0) + float(bw.weight)

    for vtx, jw in vert_weights.items():
        s = sum(jw.values())
        if s <= 1e-6:
            jw[next(iter(jw))] = 1.0
            s = 1.0
        vtx_path = '%s.vtx[%d]' % (mesh_name, vtx)
        try:
            cmds.skinPercent(skin, vtx_path,
                             transformValue=[(k, v / s) for k, v in jw.items()],
                             normalize=False)
        except Exception:
            pass


def _bind_skin_setweights(mesh_name, skin, joint_names_list,
                          mesh_data, bone_name_to_joint):
    """【无蒙皮版本】保留定义，不再调用。"""
    import maya.api.OpenMaya as om
    import maya.api.OpenMayaAnim as om_anim

    infl = cmds.skinCluster(skin, q=True, influence=True) or []
    infl_idx = {name: i for i, name in enumerate(infl)}

    vert_weights = {}
    for bone in mesh_data.bones:
        jname = bone_name_to_joint.get(bone.name)
        if jname is None:
            continue
        ji = infl_idx.get(jname)
        if ji is None:
            continue
        for bw in bone.weights:
            vert_weights.setdefault(bw.vertex, {})[ji] = \
                vert_weights.get(bw.vertex, {}).get(ji, 0.0) + float(bw.weight)

    if not vert_weights:
        return

    for vtx, jw in list(vert_weights.items()):
        s = sum(w for w in jw.values() if w > 0)
        if s <= 1e-6:
            jw[0] = 1.0
        elif abs(s - 1.0) > 1e-6:
            for k in list(jw.keys()):
                jw[k] = jw[k] / s

    shapes = cmds.listRelatives(mesh_name, shapes=True, fullPath=True) or []
    if not shapes:
        raise RuntimeError("no mesh shape under %s" % mesh_name)
    shape = shapes[0]

    sel = om.MSelectionList()
    sel.add(shape)
    shape_dag = sel.getDagPath(0)

    sel.add(skin)
    skin_mobj = sel.getDependNode(1)
    skin_fn = om_anim.MFnSkinCluster(skin_mobj)

    n_infl = len(infl)
    vtx_list = sorted(vert_weights.keys())

    comp_fn = om.MFnSingleIndexedComponent()
    vtx_comp = comp_fn.create(om.MFn.kMeshVertComponent)
    comp_fn.addElements(vtx_list)

    weights_flat = []
    for vtx_idx in vtx_list:
        jw = vert_weights[vtx_idx]
        for ji in range(n_infl):
            weights_flat.append(jw.get(ji, 0.0))

    weights_arr = om.MDoubleArray(weights_flat)
    infl_arr = om.MIntArray(range(n_infl))

    skin_fn.setWeights(shape_dag, vtx_comp, weights_arr, infl_arr, False)


def _build_animations(scene, bone_name_to_joint, anim_scale, flip_axis):
    """保留动画逻辑：骨骼仍然被创建，动画会作用到 joint 上（网格不跟随）。"""
    fps_map = {'game': 15, 'film': 24, 'pal': 25, 'ntsc': 30, 'show': 48,
               'palf': 50, 'ntscf': 60, 'millisec': 1000}
    maya_fps = fps_map.get(cmds.currentUnit(query=True, time=True), 24)
    ticks = scene.animTicksPerSecond
    if anim_scale is not None:
        scale = anim_scale
    elif ticks > 0:
        scale = float(maya_fps) / float(ticks)
    else:
        scale = 1.0

    for anim_set in scene.anims:
        for ab in anim_set.anims:
            joint_name = bone_name_to_joint.get(ab.boneName)
            if joint_name is None:
                print("[xfile_importer] anim: skip %r (not in scene)"
                      % ab.boneName)
                continue
            path = joint_name

            bind_pos = None
            bind_rot = None
            bind_scale = None
            try:
                bind_pos = cmds.getAttr(path + '.translate')[0]
                bind_rot = cmds.getAttr(path + '.rotate')[0]
                bind_scale = cmds.getAttr(path + '.scale')[0]
            except Exception:
                pass

            for t, (x, y, z) in ab.posKeys:
                mx, my, mz = _convert_point((x, y, z), flip_axis)
                time = t * scale
                if abs(time) < 1e-6:
                    if bind_pos is not None:
                        try:
                            cmds.setKeyframe(path, attribute='translateX',
                                             time=0, value=bind_pos[0])
                            cmds.setKeyframe(path, attribute='translateY',
                                             time=0, value=bind_pos[1])
                            cmds.setKeyframe(path, attribute='translateZ',
                                             time=0, value=bind_pos[2])
                        except Exception:
                            pass
                    continue
                try:
                    cmds.setKeyframe(path, attribute='translateX', time=time, value=mx)
                    cmds.setKeyframe(path, attribute='translateY', time=time, value=my)
                    cmds.setKeyframe(path, attribute='translateZ', time=time, value=mz)
                except RuntimeError:
                    pass

            for t, q in ab.rotKeys:
                e = _x_quat_to_maya_euler(q, flip_axis)
                time = t * scale
                if abs(time) < 1e-6:
                    if bind_rot is not None:
                        try:
                            cmds.setKeyframe(path, attribute='rotateX',
                                             time=0, value=bind_rot[0])
                            cmds.setKeyframe(path, attribute='rotateY',
                                             time=0, value=bind_rot[1])
                            cmds.setKeyframe(path, attribute='rotateZ',
                                             time=0, value=bind_rot[2])
                        except Exception:
                            pass
                    continue
                try:
                    cmds.setKeyframe(path, attribute='rotateX', time=time, value=math.degrees(e.x))
                    cmds.setKeyframe(path, attribute='rotateY', time=time, value=math.degrees(e.y))
                    cmds.setKeyframe(path, attribute='rotateZ', time=time, value=math.degrees(e.z))
                except RuntimeError:
                    pass

            for t, (sx, sy, sz) in ab.scaleKeys:
                time = t * scale
                if abs(time) < 1e-6:
                    if bind_scale is not None:
                        try:
                            cmds.setKeyframe(path, attribute='scaleX',
                                             time=0, value=bind_scale[0])
                            cmds.setKeyframe(path, attribute='scaleY',
                                             time=0, value=bind_scale[1])
                            cmds.setKeyframe(path, attribute='scaleZ',
                                             time=0, value=bind_scale[2])
                        except Exception:
                            pass
                    continue
                try:
                    cmds.setKeyframe(path, attribute='scaleX', time=time, value=sx)
                    cmds.setKeyframe(path, attribute='scaleY', time=time, value=sy)
                    cmds.setKeyframe(path, attribute='scaleZ', time=time, value=sz)
                except RuntimeError:
                    pass

            all_trafo_translate_zero = True
            for _t, _m16 in ab.trafoKeys:
                _mt = om.MTransformationMatrix(_x_matrix_to_maya(_m16, flip_axis))
                _tv = _mt.translation(om.MSpace.kTransform)
                if abs(_tv.x) > 1e-6 or abs(_tv.y) > 1e-6 or abs(_tv.z) > 1e-6:
                    all_trafo_translate_zero = False
                    break

            for t, m16 in ab.trafoKeys:
                mt = om.MTransformationMatrix(_x_matrix_to_maya(m16, flip_axis))
                time = t * scale
                tv = mt.translation(om.MSpace.kTransform)
                rot = mt.rotation()
                try:
                    if not all_trafo_translate_zero:
                        cmds.setKeyframe(path, attribute='translateX', time=time, value=tv.x)
                        cmds.setKeyframe(path, attribute='translateY', time=time, value=tv.y)
                        cmds.setKeyframe(path, attribute='translateZ', time=time, value=tv.z)
                    cmds.setKeyframe(path, attribute='rotateX', time=time, value=math.degrees(rot.x))
                    cmds.setKeyframe(path, attribute='rotateY', time=time, value=math.degrees(rot.y))
                    cmds.setKeyframe(path, attribute='rotateZ', time=time, value=math.degrees(rot.z))
                except RuntimeError:
                    pass


def build_scene(scene, base_path, flip_axis='Z', flip_v=True,
                anim_scale=None, tex_dir=None, import_collision=False,
                prefer_batch_skin=False, xml_mats=None):
    # 【无蒙皮版本（保留骨骼）】bone_names 恢复原逻辑 → 骨骼名对应的 Frame 建成 joint
    bone_names = _collect_bone_names(scene)
    node_to_name = {}
    node_to_xworld = {}
    x_frames_world = {}
    bone_name_to_joint = {}
    bone_name_to_joints = {}

    def create_node(node, parent_name, parent_xworld=None):
        if parent_xworld is None:
            parent_xworld = _x_identity4()

        # 累积 X 世界矩阵（行向量：local · parent）
        if node.trafoMatrix and len(node.trafoMatrix) == 16:
            local_4 = _x_mat4_from_flat(node.trafoMatrix)
        else:
            local_4 = _x_identity4()
        x_world = _x_mat4_mul(local_4, parent_xworld)
        node_to_xworld[id(node)] = x_world
        if node.name:
            x_frames_world[node.name] = x_world

        # 无名 frame：不创建 Maya 节点，子节点直接挂 parent，
        # 有 mesh 时 mesh 也挂 parent（这是原行为，必须保留）
        if not node.name:
            for c in node.children:
                create_node(c, parent_name, x_world)
            if node.meshes:
                node_to_name[id(node)] = parent_name
            return

        # 【保留骨骼创建】骨骼名对应的 Frame 建成 joint，其余建成 transform
        is_joint = node.name in bone_names
        if is_joint:
            obj_name = _create_joint(node.name, parent_name)
        else:
            obj_name = _create_transform(node.name, parent_name)
        node_to_name[id(node)] = obj_name
        if obj_name:
            bone_name_to_joint[node.name] = obj_name

        if obj_name and node.name in bone_names:
            bone_name_to_joint.setdefault(node.name, obj_name)
            bone_name_to_joints.setdefault(node.name, []).append(obj_name)

        if node.trafoMatrix:
            _apply_matrix(obj_name, node.trafoMatrix, flip_axis)
        for c in node.children:
            create_node(c, obj_name, x_world)

    # root 处理
    if scene.rootNode is not None:
        if scene.rootNode.name == '$dummy_root' or not scene.rootNode.name:
            for child in scene.rootNode.children:
                create_node(child, None)
        else:
            # 【保留骨骼创建】root 也按骨骼名判断
            is_root_joint = scene.rootNode.name in bone_names
            if is_root_joint:
                root_name = _create_joint(scene.rootNode.name, None)
            else:
                root_name = _create_transform(scene.rootNode.name, None)
            node_to_name[id(scene.rootNode)] = root_name
            if root_name:
                bone_name_to_joint[scene.rootNode.name] = root_name
                bone_name_to_joints.setdefault(scene.rootNode.name, []).append(root_name)
            if scene.rootNode.trafoMatrix:
                _apply_matrix(root_name, scene.rootNode.trafoMatrix, flip_axis)
            if scene.rootNode.trafoMatrix and len(scene.rootNode.trafoMatrix) == 16:
                root_local = [[float(scene.rootNode.trafoMatrix[r*4+c]) for c in range(4)]
                              for r in range(4)]
            else:
                root_local = _x_identity4()
            root_xworld = root_local
            node_to_xworld[id(scene.rootNode)] = root_xworld
            for c in scene.rootNode.children:
                create_node(c, root_name, root_xworld)


    def process_meshes(node):
        parent_name = node_to_name.get(id(node))
        
        # 根据当前节点名，查找对应的 XML 贴图信息
        xml_mat_props = None
        if xml_mats and node.name:
            if node.name in xml_mats:
                xml_mat_props = xml_mats[node.name]
            elif (node.name + "_mesh") in xml_mats:
                xml_mat_props = xml_mats[node.name + "_mesh"]
            else:
                # 如果匹配不到，尝试用前缀匹配（比如 trak_001 匹配 trak_）
                for k, v in xml_mats.items():
                    if node.name.startswith(k) or k.startswith(node.name):
                        xml_mat_props = v
                        break

        # 【调试】看看到底匹配到了没有（用 _VERBOSE 开启）
        if node.meshes and _VERBOSE:
            print(f"[DEBUG] 节点 '{node.name}' 匹配结果: {bool(xml_mat_props)}")

        for idx, mesh_data in enumerate(node.meshes):
            base_hint = node.name or 'mesh'
            hint = ('%s_mesh%d' % (base_hint, idx + 1)
                    if len(node.meshes) > 1 else '%s_mesh' % base_hint)

            name_lower = (hint or '').lower()
            is_collision = ('cdt' in name_lower or 'collision' in name_lower
                            or '_coll' in name_lower)
            if is_collision and not import_collision:
                print("[xfile_importer] skip collision mesh: %r" % hint)
                continue

            # --- 【无蒙皮版本（保留骨骼）】网格创建：不管有没有 bones，
            #     都挂到所属 Frame 下，不做任何预乘 ---
            mesh_name = _create_mesh_shape(
                mesh_data, parent_name, flip_axis, flip_v, name_hint=hint)
            if mesh_name is None:
                continue
            # -------------------------

            if is_collision:
                _, sg = _create_collision_material()
                if not mesh_data.faceMaterials:
                    mesh_data.faceMaterials = [0] * len(mesh_data.posFaces)
                _assign_materials(mesh_name, mesh_data.faceMaterials, [sg])
            else:
                sg_list = []
                
                # 从 XML 配置中提取共享材质名
                xml_mat_name = None
                if xml_mat_props:
                    xml_mat_name = xml_mat_props.get('_MaterialName')

                if not mesh_data.materials:
                    default_mat = Material()
                    default_mat.name = xml_mat_name or ((hint or 'mesh') + '_default')
                    default_mat.diffuse = (0.7, 0.7, 0.7, 1.0)
                    if xml_mat_props:
                        default_mat.xml_props = dict(xml_mat_props)
                    
                    try:
                        _, sg = _create_material_node(default_mat, base_path, tex_dir=tex_dir)
                        sg_list.append(sg)
                    except Exception as e:
                        print("[xfile_importer] default material failed: %r" % e)
                    if not mesh_data.faceMaterials:
                        mesh_data.faceMaterials = [0] * len(mesh_data.posFaces)
                else:
                    for mat in mesh_data.materials:
                        resolved = _resolve_material(mat, scene.globalMaterials)
                        if xml_mat_props:
                            resolved.xml_props = dict(xml_mat_props)
                            if xml_mat_name:
                                resolved.name = xml_mat_name
                            
                        try:
                            _, sg = _create_material_node(
                                resolved, base_path, tex_dir=tex_dir)
                            sg_list.append(sg)
                        except Exception as e:
                            print("[xfile_importer] material %r failed: %r"
                                  % (mat.name, e))
                if not mesh_data.faceMaterials and mesh_data.materials:
                    mesh_data.faceMaterials = [0] * len(mesh_data.posFaces)
                try:
                    _assign_materials(mesh_name, mesh_data.faceMaterials, sg_list)
                except Exception as e:
                    print("[xfile_importer] assign materials failed: %r" % e)

            # 【无蒙皮版本（保留骨骼）】不创建 skinCluster，不写权重
        for c in node.children:
            process_meshes(c)

    if scene.rootNode is not None:
        process_meshes(scene.rootNode)

    for idx, mesh_data in enumerate(scene.globalMeshes):
        hint = 'globalMesh%d' % idx
        mesh_name = _create_mesh_shape(
            mesh_data, None, flip_axis, flip_v, name_hint=hint)
        if mesh_name is None:
            continue
        sg_list = []
        for mat in mesh_data.materials:
            resolved = _resolve_material(mat, scene.globalMaterials)
            _, sg = _create_material_node(resolved, base_path)
            sg_list.append(sg)
        _assign_materials(mesh_name, mesh_data.faceMaterials, sg_list)

    # 动画保留调用：bone_name_to_joint 有骨骼名 → 动画作用到 joint 上
    if scene.anims:
        _build_animations(scene, bone_name_to_joint, anim_scale, flip_axis)

    # 汇总
    total_meshes = 0
    total_verts = 0
    total_tris = 0
    skinned_meshes = 0
    total_joints = 0

    def walk(node):
        nonlocal total_meshes, total_verts, total_tris, skinned_meshes
        if node is None: return
        for m in node.meshes:
            total_meshes += 1
            total_verts += len(m.positions)
            total_tris += sum(max(0, len(f.indices) - 2) for f in m.posFaces)
            if m.bones: skinned_meshes += 1
        for c in node.children: walk(c)

    walk(scene.rootNode)
    total_joints = len(bone_name_to_joint)
    print(f"[xfile_importer] === 导入汇总 ===")
    print(f"  meshes:   {total_meshes}  (skinned: {skinned_meshes})")
    print(f"  verts:    {total_verts}")
    print(f"  tris:     {total_tris}")
    print(f"  joints:   {total_joints}")
    print(f"  materials: {len(_XFILE_MATERIAL_CACHE)}")

# ---------------------------------------------------------------------------
# 后处理：重复 mesh 重命名
# ---------------------------------------------------------------------------

def _rename_duplicate_meshes():
    renamed = 0
    seen = set()

    for m in cmds.ls(type='mesh'):
        try:
            if cmds.getAttr(m + '.intermediateObject'):
                continue
        except Exception:
            continue

        parent_path = cmds.listRelatives(m, parent=True)
        if not parent_path:
            continue
        t = parent_path[0]

        if not (t == 'mesh' or t.startswith('mesh_')):
            continue

        hint = None
        skin = cmds.listConnections(m, type='skinCluster') or []
        if skin:
            infl = cmds.skinCluster(skin[0], q=True, influence=True) or []
            if infl:
                hint = infl[0]

        if not hint:
            hint = 'mesh'

        candidate = hint
        i = 0
        while cmds.objExists(candidate) or candidate in seen:
            i += 1
            candidate = '%s_mesh%d' % (hint, i)
        try:
            cmds.rename(t, candidate)
            seen.add(candidate)
            renamed += 1
        except Exception as e:
            print("[xfile_importer] rename mesh %s failed: %r" % (t, e))

    if renamed:
        print("[xfile_importer] renamed %d mesh(es) with meaningful names"
              % renamed)


# ===========================================================================
# Section 3: 导入入口
# ===========================================================================

_VALID_AXES = ('X', 'Z', 'None', '')


def import_x_file(path, flip_axis='Z', flip_v=True, anim_scale=None,
                  tex_dir=None, import_collision=False,
                  import_socketpoints=False):
    """从文件路径读取并导入 XFile。返回导入的 Scene。"""

    # 未显式指定 tex_dir 时，自动读取 UI 里保存的 Textures folder
    if not tex_dir:
        try:
            tex_dir = _load_tex_dir() or None
        except Exception:
            tex_dir = None

    with open(path, 'rb') as f:
        buffer = f.read()

    # 若文件带内嵌 XML 头，尝试把材质 XML 塞进 scene.globalMaterials
    embedded_xml, _ = _extract_embedded_xml(path)

    # 2. 无内嵌 XML → 尝试同名 .xml
    if not embedded_xml:
        xml_path = _find_sibling_xml(path)
        if xml_path:
            try:
                with open(xml_path, 'r', encoding='utf-8', errors='replace') as f:
                    embedded_xml = f.read()
                print("[xfile_importer] auto-loaded material XML: %s"
                      % os.path.basename(xml_path))
            except Exception as e:
                print("[xfile_importer] failed to read sibling xml %s: %r"
                      % (xml_path, e))

    # socketpoints 逻辑必须在 embedded_xml 定义之后
    if embedded_xml and import_socketpoints:
        sps = parse_xml_socketpoints(embedded_xml)
        if sps:
            created = create_socket_locators(sps, flip_axis=flip_axis)
            print("[xfile_importer] created %d/%d socket locator(s)"
                  % (len(created), len(sps)))

    parser = XFileParser(buffer)
    base_path = os.path.dirname(path)

    # 【新增】无论是否打印，都先算一次 bone bindings 并缓存，
    # 供"View Bone Bindings"按钮直接浏览（不需要重新选择文件）
    global _LAST_BONE_BINDINGS
    try:
        _bind_text = format_bone_bindings(
            parser.scene,
            title='Bone Bindings of %s' % os.path.basename(path))
        _LAST_BONE_BINDINGS = {'path': path, 'text': _bind_text}
        if _PRINT_BONE_BINDINGS:
            # 【优化】默认只打一行汇总，避免长文本拖慢 Script Editor
            if _PRINT_BONE_BINDINGS_VERBOSE:
                print(_bind_text)
            else:
                b2m, m2b = collect_bone_bindings(parser.scene)
                print("[xfile_importer] bone bindings: %d bone(s) / %d mesh(es) "
                      "(use 'View Bone Bindings' for full list)"
                      % (len(b2m), len(m2b)))
    except Exception as e:
        print("[xfile_importer] bone bindings cache failed: %r" % e)

    xml_mats = {}
    if embedded_xml:
        xml_mats = parse_xml_materials(embedded_xml)
        if xml_mats:
            _inject_xml_materials(parser.scene, xml_mats)

    _XFILE_MATERIAL_CACHE.clear()

    # 【性能】关掉 undo 记录。导入本来不该撤销，大文件时
    # openChunk 会把每一条节点创建都记入 undo 栈，Maya 主线程会卡住。
    prev_undo = True
    try:
        cmds.flushUndo()
        prev_undo = cmds.undoInfo(q=True, state=True)
        cmds.undoInfo(state=False)
    except Exception:
        pass

    try:
        build_scene(parser.scene, base_path,
                    flip_axis=flip_axis, flip_v=flip_v,
                    anim_scale=anim_scale,
                    tex_dir=tex_dir,
                    import_collision=import_collision,
                    prefer_batch_skin=parser.isCompressed,
                    xml_mats=xml_mats)
        _rename_duplicate_meshes()
    finally:
        try:
            cmds.flushUndo()
            cmds.undoInfo(state=prev_undo)
        except Exception:
            pass

    try:
        cmds.currentTime(0, edit=True)
    except Exception:
        pass

    return parser.scene


def _inject_xml_materials(scene, xml_mats):
    """把 XML 材质（含 AlbedoMap 等路径）合并到 Material 对象。"""
    if not xml_mats:
        return
    all_mats = list(scene.globalMaterials)

    def visit(node):
        if node is None:
            return
        for mesh in node.meshes:
            for m in mesh.materials:
                all_mats.append(m)
        for c in node.children:
            visit(c)

    visit(scene.rootNode)
    for mesh in scene.globalMeshes:
        for m in mesh.materials:
            all_mats.append(m)

    unique_mats = {m.name: m for m in all_mats if m.name}
    # 【优化】长名优先匹配（更精确，模糊匹配命中率更高、次数更少）
    xml_names = sorted(xml_mats.keys(), key=len, reverse=True)
    
    if not xml_names:
        return
        
    print(f"[xfile_importer] 找到 X 材质 {len(unique_mats)} 个, XML 材质 {len(xml_names)} 个")

    for x_name, m in unique_mats.items():
        if x_name in xml_mats:
            m.xml_props = dict(xml_mats[x_name])
            print(f"[xfile_importer] 材质 '{x_name}' 精确匹配成功")
            continue
            
        matched = False
        for xml_name in xml_names:
            if xml_name in x_name or x_name in xml_name:
                m.xml_props = dict(xml_mats[xml_name])
                print(f"[xfile_importer] 材质 '{x_name}' 模糊匹配到 '{xml_name}'")
                matched = True
                break
                
        if not matched:
            first_xml_name = xml_names[0]
            m.xml_props = dict(xml_mats[first_xml_name])
            print(f"[xfile_importer] 材质 '{x_name}' 强制绑定至 XML 材质 '{first_xml_name}'")

    for m in all_mats:
        props = getattr(m, 'xml_props', {})
        try:
            dc = props.get('DiffuseColor')
            if dc and m.diffuse == (0.0, 0.0, 0.0, 1.0):
                parts = [float(x) for x in dc.replace(',', ' ').split()]
                if len(parts) >= 3:
                    a = parts[3] if len(parts) >= 4 else 1.0
                    m.diffuse = (parts[0], parts[1], parts[2], a)
        except Exception:
            pass


# ===========================================================================
# Section 4: MPxFileTranslator
# ===========================================================================

kTranslatorName = "DirectX XFile Importer"
kDefaultOptions = "flip_axis=Z;flip_v=1;anim_scale="


def _resolve_filepath(file_object):
    """从 MPxFileObject 取文件路径（与 Section 2 的 _resolve_path 无关）。"""
    for attr in ('resolvedFullName', 'fullName'):
        if hasattr(file_object, attr):
            try:
                p = getattr(file_object, attr)()
                if p:
                    return p
            except Exception:
                pass
    return str(file_object)


class XFileTranslator(OpenMayaMPx.MPxFileTranslator):
    def __init__(self):
        OpenMayaMPx.MPxFileTranslator.__init__(self)
        self._flip_axis = 'Z'
        self._flip_v = True
        self._anim_scale = None
        self._import_collision = False

    def haveReadMethod(self): return True
    def haveWriteMethod(self): return False
    def haveReferenceMethod(self): return False
    def haveNamespaceSupport(self): return False
    def defaultExtension(self): return "x"
    def filter(self): return "*.x;*.X"
    def hasOptions(self): return True
    def options(self): return ""

    def readOptions(self, s):
        if not s:
            return
        for pair in s.split(';'):
            pair = pair.strip()
            if '=' not in pair:
                continue
            k, v = pair.split('=', 1)
            k, v = k.strip(), v.strip()
            if k == 'flip_axis':
                if v in _VALID_AXES:
                    self._flip_axis = None if v in ('None', '') else v
            elif k == 'flip_v':
                self._flip_v = v in ('1', 'True', 'true', 'on')
            elif k == 'import_collision':
                self._import_collision = v in ('1', 'True', 'true', 'on')
            elif k == 'anim_scale' and v:
                try:
                    self._anim_scale = float(v)
                except ValueError:
                    pass

    def writeOptions(self, s):
        return ('flip_axis=%s;flip_v=%d;anim_scale=%s;import_collision=%d'
                % (self._flip_axis, 1 if self._flip_v else 0,
                   '' if self._anim_scale is None else str(self._anim_scale),
                   1 if self._import_collision else 0))

    def identify(self, fo, buf):
        if _resolve_filepath(fo).lower().endswith('.x'):
            return OpenMayaMPx.MPxFileTranslator.kCouldBeMyFileType
        return OpenMayaMPx.MPxFileTranslator.kNotMyFileType

    def reader(self, fo, opt, mode):
        ok = (OpenMayaMPx.MPxFileTranslator.kOpenAccessMode,
              OpenMayaMPx.MPxFileTranslator.kImportAccessMode)
        if mode not in ok:
            return OpenMayaMPx.MPxFileTranslator.kFailure
        try:
            self.readOptions(opt)
            path = _resolve_filepath(fo)
            if not path or not os.path.isfile(path):
                cmds.error('XFile: file not found: %s' % path)
                return OpenMayaMPx.MPxFileTranslator.kFailure
            import_x_file(path, self._flip_axis, self._flip_v,
                          self._anim_scale,
                          tex_dir=_load_tex_dir(),
                          import_collision=self._import_collision)
            cmds.inViewMessage(amg='<hl>Imported:</hl> %s'
                                   % os.path.basename(path),
                               pos='botCenter', fade=True)
            return OpenMayaMPx.MPxFileTranslator.kSuccess
        except ImportError as e:
            cmds.error('XFile parse error: %s' % e)
            return OpenMayaMPx.MPxFileTranslator.kFailure
        except Exception as e:
            cmds.error('XFile import failed: %s' % e)
            traceback.print_exc()
            return OpenMayaMPx.MPxFileTranslator.kFailure


def create_translator():
    return OpenMayaMPx.asMPxPtr(XFileTranslator())


# ===========================================================================
# Section 5: UI + 菜单
# ===========================================================================

_MENU_NAME = "mudrunnerXMenu"
_UI_WINDOW = "mudrunnerXImporterWin"
_XML_WINDOW = "mudrunnerXmlViewerWin"
_MAT_XML_WINDOW = "mudrunnerMatXmlWin"
_BONE_BIND_WINDOW = "mudrunnerBoneBindWin"

_OPT_TEX_DIR     = "mudrunnerTexDir"
_OPT_LAST_MESH   = "mudrunnerLastXFile"


# ---------- optionVar 持久化 ----------
# 【优化】加 1 元缓存，避免每次 _load_tex_dir / _load_last_mesh_path 都读 optionVar
_TEX_DIR_CACHE = [None]
_LAST_MESH_CACHE = [None]


def _load_tex_dir():
    if _TEX_DIR_CACHE[0] is not None:
        return _TEX_DIR_CACHE[0]
    try:
        if cmds.optionVar(exists=_OPT_TEX_DIR):
            _TEX_DIR_CACHE[0] = cmds.optionVar(q=_OPT_TEX_DIR) or ""
            return _TEX_DIR_CACHE[0]
    except Exception:
        pass
    _TEX_DIR_CACHE[0] = ""
    return ""


def _save_tex_dir(path):
    _TEX_DIR_CACHE[0] = path or ""
    try:
        cmds.optionVar(sv=(_OPT_TEX_DIR, path or ""))
    except Exception:
        pass


def _load_last_mesh_path():
    if _LAST_MESH_CACHE[0] is not None:
        return _LAST_MESH_CACHE[0]
    try:
        if cmds.optionVar(exists=_OPT_LAST_MESH):
            _LAST_MESH_CACHE[0] = cmds.optionVar(q=_OPT_LAST_MESH) or ""
            return _LAST_MESH_CACHE[0]
    except Exception:
        pass
    _LAST_MESH_CACHE[0] = ""
    return ""


def _save_last_mesh_path(path):
    _LAST_MESH_CACHE[0] = path or ""
    try:
        cmds.optionVar(sv=(_OPT_LAST_MESH, path or ""))
    except Exception:
        pass


# ---------- UI 控件回调 ----------

def _browse_tex_dir(*args):
    kwargs = dict(fileMode=3, dialogStyle=2,
                  caption="Select Textures folder")
    cur = ""
    try:
        cur = cmds.textFieldButtonGrp("xTexDir", q=True, text=True) or ""
    except Exception:
        pass
    if not cur:
        cur = _load_tex_dir()
    if cur and os.path.isdir(cur):
        kwargs["startingDirectory"] = cur
    result = cmds.fileDialog2(**kwargs)
    if result:
        cmds.textFieldButtonGrp("xTexDir", edit=True, text=result[0])
        _save_tex_dir(result[0])


def _on_tex_dir_changed(*args):
    try:
        v = cmds.textFieldButtonGrp("xTexDir", q=True, text=True) or ""
    except Exception:
        v = ""
    _save_tex_dir(v)


def _get_tex_dir_for_import():
    tex_dir = ""
    if cmds.textFieldButtonGrp("xTexDir", exists=True):
        tex_dir = cmds.textFieldButtonGrp("xTexDir", q=True, text=True) or ""
    if not tex_dir:
        tex_dir = _load_tex_dir()
    return tex_dir


# ---------- XML 查看器 ----------

def _format_xml_for_display(xml, max_chars=4 * 1024 * 1024):
    if not xml:
        return "(empty)"
    pretty = xml.replace("><", ">\n<")
    if len(pretty) > max_chars:
        pretty = pretty[:max_chars] + ("\n\n... (truncated at %d chars, "
                                       "original %d chars)"
                                       % (max_chars, len(xml)))
    return pretty


def _show_xml_window(title, xml_text, note=""):
    if cmds.window(_XML_WINDOW, exists=True):
        cmds.deleteUI(_XML_WINDOW)
    cmds.window(_XML_WINDOW, title=title, width=1000, height=800,
                sizeable=True)
    form = cmds.formLayout()

    if note:
        note_text = cmds.text(label=note, align="left",
                              font="smallObliqueLabelFont")
        sf = cmds.scrollField(editable=False, wordWrap=False,
                              text=_format_xml_for_display(xml_text))
        cmds.formLayout(form, edit=True,
                        attachForm=[(note_text, 'top', 6),
                                    (note_text, 'left', 6),
                                    (note_text, 'right', 6),
                                    (sf, 'left', 6),
                                    (sf, 'right', 6),
                                    (sf, 'bottom', 6)],
                        attachControl=[(sf, 'top', 6, note_text)])
    else:
        sf = cmds.scrollField(editable=False, wordWrap=False,
                              text=_format_xml_for_display(xml_text))
        cmds.formLayout(form, edit=True,
                        attachForm=[(sf, 'top', 6),
                                    (sf, 'left', 6),
                                    (sf, 'right', 6),
                                    (sf, 'bottom', 6)])
    cmds.showWindow(_XML_WINDOW)


def _prompt_for_xfile_path(caption="Select an X file to inspect"):
    kwargs = dict(fileMode=1, dialogStyle=2, caption=caption,
                  fileFilter="DirectX XFile (*.x *.X);;All files (*)")
    start = ""
    last = _load_last_mesh_path()
    if last and os.path.isfile(last):
        start = os.path.dirname(last)
    if not start:
        start = _load_tex_dir()
    if start and os.path.isdir(start):
        kwargs["startingDirectory"] = start
    files = cmds.fileDialog2(**kwargs)
    return files[0] if files else None


def _view_xml_from_last_or_prompt(*args):
    path = _load_last_mesh_path()
    if path and os.path.isfile(path):
        xml, _ = _extract_embedded_xml(path)
        if not xml:
            cmds.warning("No embedded XML header found in %s "
                         "(likely a standard DirectX .x file)."
                         % os.path.basename(path))
            return
        _show_xml_window("MudRunner XML - " + os.path.basename(path),
                         xml,
                         "XML header from: %s (%d bytes)"
                         % (os.path.basename(path), len(xml)))
        return

    path = _prompt_for_xfile_path()
    if not path:
        return
    _save_last_mesh_path(path)
    xml, _ = _extract_embedded_xml(path)
    if not xml:
        cmds.warning("No embedded XML header found in %s."
                     % os.path.basename(path))
        return
    _show_xml_window("MudRunner XML - " + os.path.basename(path),
                     xml,
                     "XML header from: %s (%d bytes)"
                     % (os.path.basename(path), len(xml)))


def _find_sibling_xml(x_path):
    if not x_path or not os.path.isfile(x_path):
        return None
    folder = os.path.dirname(x_path)
    stem = os.path.splitext(os.path.basename(x_path))[0]
    if not folder or not os.path.isdir(folder) or not stem:
        return None

    exact = os.path.join(folder, stem + ".xml")
    if os.path.isfile(exact):
        return exact

    try:
        for name in os.listdir(folder):
            root, ext = os.path.splitext(name)
            if root.lower() == stem.lower() and ext.lower() == ".xml":
                p = os.path.join(folder, name)
                if os.path.isfile(p):
                    return p
    except OSError:
        pass
    return None


def _show_material_dialog(*args):
    files = []

    last_x = _load_last_mesh_path()
    auto_xml = _find_sibling_xml(last_x)
    if auto_xml:
        files = [auto_xml]
        print("[xfile_importer] auto-selected material XML: %s" % auto_xml)
        try:
            cmds.inViewMessage(
                amg="MudRunner: auto-detected material XML "
                    "<hl>%s</hl> next to last imported X file."
                    % os.path.basename(auto_xml),
                pos="botCenter", fade=True)
        except Exception:
            pass
    else:
        kwargs = dict(
            fileMode=4, dialogStyle=2,
            caption="Select MudRunner material XML file(s) to view / import",
            fileFilter="XML files (*.xml);;All files (*)")
        if last_x and os.path.isfile(last_x):
            kwargs["startingDirectory"] = os.path.dirname(last_x)
        elif _load_tex_dir() and os.path.isdir(_load_tex_dir()):
            kwargs["startingDirectory"] = _load_tex_dir()
        files = cmds.fileDialog2(**kwargs)
        if not files:
            return

    loaded = []
    for path in files:
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                xml = fh.read()
            loaded.append((path, xml))
        except Exception as e:
            cmds.warning("%s: %s" % (os.path.basename(path), e))
    if not loaded:
        return

    parts = []
    for path, xml in loaded:
        parts.append("=== %s (%d chars) ===" % (path, len(xml)))
        parts.append(xml)
        parts.append("")
    combined = "\n".join(parts)

    _show_material_xml_viewer(combined, loaded, files[0])


def _show_material_xml_viewer(combined_xml, loaded_files, first_path):
    if cmds.window(_MAT_XML_WINDOW, exists=True):
        cmds.deleteUI(_MAT_XML_WINDOW)

    cmds.window(_MAT_XML_WINDOW,
                title="MudRunner Material XML - " + os.path.basename(first_path),
                width=1000, height=800, sizeable=True)
    form = cmds.formLayout()

    note = cmds.text(
        label="Material XML from: %s  (%d file(s), %d chars total)"
              % (os.path.basename(first_path), len(loaded_files),
                 len(combined_xml)),
        align="left", font="smallObliqueLabelFont")

    sf = cmds.scrollField(editable=False, wordWrap=False,
                          text=_format_xml_for_display(combined_xml))

    import_btn = cmds.button(
        label="Import These Materials", height=30,
        command=lambda *a: _do_import_material_xml(loaded_files, first_path))
    repick_btn = cmds.button(
        label="Pick different XML...", height=30,
        command=lambda *a: _repick_material_xml())
    close_btn = cmds.button(
        label="Close", height=30,
        command=lambda *a: cmds.deleteUI(_MAT_XML_WINDOW))

    cmds.formLayout(
        form, edit=True,
        attachForm=[
            (note, 'top', 6),
            (note, 'left', 6),
            (note, 'right', 6),
            (sf, 'left', 6),
            (sf, 'right', 6),
            (import_btn, 'left', 6),
            (import_btn, 'bottom', 6),
            (repick_btn, 'bottom', 6),
            (close_btn, 'right', 6),
            (close_btn, 'bottom', 6),
        ],
        attachControl=[
            (sf, 'top', 6, note),
            (sf, 'bottom', 6, import_btn),
        ],
        attachPosition=[
            (import_btn, 'right', 0, 33),
            (repick_btn, 'left', 0, 33),
            (repick_btn, 'right', 0, 66),
            (close_btn, 'left', 0, 66),
        ])

    cmds.showWindow(_MAT_XML_WINDOW)


def _do_import_material_xml(loaded_files, first_path):
    tex_dir = _get_tex_dir_for_import()
    base_path = os.path.dirname(first_path) if first_path else ""
    count = 0
    failed = 0
    for path, xml in loaded_files:
        xml_mats = parse_xml_materials(xml)
        for name, props in xml_mats.items():
            mat = Material()
            mat.name = name
            mat.xml_props = dict(props)
            try:
                dc = props.get('DiffuseColor')
                if dc:
                    parts = [float(x) for x in dc.replace(',', ' ').split()]
                    if len(parts) >= 3:
                        a = parts[3] if len(parts) >= 4 else 1.0
                        mat.diffuse = (parts[0], parts[1], parts[2], a)
                mat.specularExponent = 15.0
            except Exception:
                pass
            try:
                _create_material_node(mat, base_path, tex_dir=tex_dir)
                count += 1
            except Exception as e:
                failed += 1
                print("[xfile_importer] material %r failed: %r"
                      % (name, e))

    if count or failed:
        cmds.inViewMessage(
            amg="MudRunner: built/updated <hl>%d</hl> material(s)%s."
                % (count, (", %d failed" % failed) if failed else ""),
            pos="midCenter", fade=True)

    if cmds.window(_MAT_XML_WINDOW, exists=True):
        try:
            cmds.deleteUI(_MAT_XML_WINDOW)
        except Exception:
            pass


def _repick_material_xml():
    if cmds.window(_MAT_XML_WINDOW, exists=True):
        cmds.deleteUI(_MAT_XML_WINDOW)
    saved = _load_last_mesh_path()
    _save_last_mesh_path("")
    try:
        _show_material_dialog()
    finally:
        _save_last_mesh_path(saved)


# ---------- 骨骼绑定查看器 ----------

def _delete_bone_bind_window():
    if cmds.window(_BONE_BIND_WINDOW, exists=True):
        try:
            cmds.deleteUI(_BONE_BIND_WINDOW)
        except Exception:
            pass


def _show_bone_bindings_window(path, text):
    """用已缓存好的文本打开骨骼绑定窗口（不再解析文件）。"""
    _delete_bone_bind_window()
    cmds.window(_BONE_BIND_WINDOW,
                title="Bone Bindings - " + os.path.basename(path),
                width=1000, height=800, sizeable=True)
    form = cmds.formLayout()

    note = cmds.text(
        label="X File: %s   (cached from last import / view)"
              % path,
        align="left", font="smallObliqueLabelFont")
    sf = cmds.scrollField(editable=False, wordWrap=False, text=text)

    repick_btn = cmds.button(
        label="Pick another X file...", height=30,
        command=lambda *a: (_delete_bone_bind_window(),
                            _view_bone_bindings(force_pick=True)))
    close_btn = cmds.button(
        label="Close", height=30,
        command=lambda *a: _delete_bone_bind_window())

    cmds.formLayout(
        form, edit=True,
        attachForm=[
            (note, 'top', 6),
            (note, 'left', 6),
            (note, 'right', 6),
            (sf, 'left', 6),
            (sf, 'right', 6),
            (repick_btn, 'left', 6),
            (repick_btn, 'bottom', 6),
            (close_btn, 'right', 6),
            (close_btn, 'bottom', 6),
        ],
        attachControl=[
            (sf, 'top', 6, note),
            (sf, 'bottom', 6, repick_btn),
        ],
        attachPosition=[
            (repick_btn, 'right', 0, 50),
            (close_btn, 'left', 0, 50),
        ])

    cmds.showWindow(_BONE_BIND_WINDOW)


def _parse_bone_bindings_to_cache(path):
    """解析 X 文件，缓存 bone bindings（如果成功返回 True）。"""
    global _LAST_BONE_BINDINGS
    try:
        with open(path, 'rb') as f:
            buffer = f.read()
        parser = XFileParser(buffer)
    except Exception as e:
        cmds.warning("Bone Bindings: 解析失败 %s: %r"
                     % (os.path.basename(path), e))
        traceback.print_exc()
        return False

    text = format_bone_bindings(
        parser.scene,
        title='Bone Bindings of %s' % os.path.basename(path))
    _LAST_BONE_BINDINGS = {'path': path, 'text': text}
    return True


def _view_bone_bindings(force_pick=False, *args):
    """查看骨骼绑定。

    行为：
      - force_pick=True → 强制弹文件选择对话框
      - force_pick=False（默认）→ 若有上次导入/查看的缓存，直接显示
      - 无缓存 且 force_pick=False → 弹文件选择对话框
    """
    if not force_pick and _LAST_BONE_BINDINGS:
        _show_bone_bindings_window(_LAST_BONE_BINDINGS['path'],
                                   _LAST_BONE_BINDINGS['text'])
        return

    path = _prompt_for_xfile_path(
        caption="Select an X file to inspect bone bindings")
    if not path:
        return

    if not _parse_bone_bindings_to_cache(path):
        return

    _show_bone_bindings_window(_LAST_BONE_BINDINGS['path'],
                               _LAST_BONE_BINDINGS['text'])


def _menu_cb_bone_bindings(*args):
    try:
        _view_bone_bindings()
    except Exception:
        traceback.print_exc()


# ---------- 导入流程 ----------

def _get_ui_options():
    flip_axis = 'Z'
    flip_v = True
    anim_scale = None
    import_collision = False
    import_socketpoints = True
    if cmds.optionMenu("xFlipAxis", exists=True):
        label = cmds.optionMenu("xFlipAxis", q=True, value=True) or 'Z'
        flip_axis = None if label == 'None' else label
    if cmds.checkBox("xFlipV", exists=True):
        flip_v = cmds.checkBox("xFlipV", q=True, v=True)
    if cmds.checkBox("xImportCollision", exists=True):
        import_collision = cmds.checkBox("xImportCollision", q=True, v=True)
    if cmds.checkBox("xImportSocketpoints", exists=True):
        import_socketpoints = cmds.checkBox("xImportSocketpoints", q=True, v=True)
    if cmds.textFieldGrp("xAnimScale", exists=True):
        text = cmds.textFieldGrp("xAnimScale", q=True, text=True) or ""
        text = text.strip()
        if text:
            try:
                anim_scale = float(text)
            except ValueError:
                anim_scale = None
    return flip_axis, flip_v, anim_scale, import_collision, import_socketpoints

def _do_import_files(*args):
    files = cmds.fileDialog2(
        fileMode=4, dialogStyle=2,
        caption="Select MudRunner X File(s)",
        fileFilter="DirectX XFile (*.x *.X);;All files (*)")
    if not files:
        return

    _save_last_mesh_path(files[0])

    flip_axis, flip_v, anim_scale, import_collision, import_socketpoints = _get_ui_options()
    tex_dir = _get_tex_dir_for_import()

    total = 0
    failed = []
    for path in files:
        try:
            scene = import_x_file(path, flip_axis, flip_v, anim_scale,
                                  tex_dir=tex_dir,
                                  import_collision=import_collision,
                                  import_socketpoints=import_socketpoints)

            def count(node):
                if node is None:
                    return 0
                return len(node.meshes) + sum(count(c) for c in node.children)

            total += len(scene.globalMeshes) + count(scene.rootNode)
        except Exception as e:
            failed.append('%s: %r' % (os.path.basename(path), e))
            traceback.print_exc()
    if failed:
        cmds.warning("XFile import failed for: " + "; ".join(failed))
    if total:
        cmds.inViewMessage(amg="MudRunner: imported <hl>%d</hl> mesh(es)."
                               % total, pos="midCenter", fade=True)


def _show_about(*args):
    cmds.confirmDialog(
        title="About MudRunner X Importer",
        message=("MudRunner X (.x) Importer\n"
                 "Version 1.5.0 【无蒙皮版本（保留骨骼）· 性能优化版】\n\n"
                 "Formats: txt / bin / tzip / bzip\n"
                 "Imports: meshes, materials, skeleton (joints only),\n"
                 "         embedded XML materials, SocketPoints.\n"
                 "         (No skinCluster / skinning weights.)\n\n"
                 "Tools: Bone Bindings Viewer (menu / button).\n"
                 "       Reuses the last imported X's bindings if available.\n\n"
                 "UI options: textures folder, collision toggle,\n"
                 "            XML viewer, material XML import.\n\n"
                 "Performance: texture index, per-face UV bulk, cached "
                 "optionVars, quiet debug prints."),
        button=["OK"], defaultButton="OK")


# ---------- 主窗口 ----------

def show_ui():
    if cmds.window(_UI_WINDOW, exists=True):
        cmds.deleteUI(_UI_WINDOW)
    cmds.window(_UI_WINDOW, title="MudRunner X Importer",
                width=480, sizeable=True)
    cmds.columnLayout(adjustableColumn=True, rowSpacing=8,
                      columnAttach=("both", 10))

    cmds.separator(height=6, style="none")
    cmds.text(label="MudRunner X Importer",
              font="boldLabelFont", align="left")
    cmds.text(label="Import .x (DirectX) with materials, skeleton (no skinning), "
                    "SocketPoints.",
              align="left", font="smallObliqueLabelFont")
    cmds.separator(height=6, style="in")

    cmds.textFieldButtonGrp(
        "xTexDir", label="Textures folder:",
        text=_load_tex_dir(),
        buttonLabel="Browse",
        buttonCommand=_browse_tex_dir,
        changeCommand=_on_tex_dir_changed,
        adjustableColumn=2, columnWidth3=(100, 290, 70))

    cmds.optionMenu("xFlipAxis", label="Flip axis:")
    cmds.menuItem(label="X")
    cmds.menuItem(label="Z (DirectX default)")
    cmds.menuItem(label="None")

    cmds.checkBox("xFlipV", label="Flip V (UV convention)", value=True)
    cmds.checkBox("xImportCollision",
                  label="Import collision meshes (bright orange)",
                  value=False)
    cmds.checkBox("xImportSocketpoints", label="Import SocketPoints as locators", value=True)
    cmds.checkBox("xImportNormals", label="Import custom normals", value=False)
    cmds.textFieldGrp("xAnimScale",
                      label="Set Anim scale (empty = auto):", text="")

    cmds.separator(height=8, style="in")
    cmds.button(label="Import X File(s)...",
                height=32, command=_do_import_files)
    cmds.button(label="View / Reimport Material XML...",
                height=28, command=lambda *a: _show_material_dialog())
    cmds.button(label="View Bone Bindings (last import / from X file)...",
                height=28, command=_view_bone_bindings)
    cmds.separator(height=6, style="in")
    cmds.button(label="About / Help", height=22, command=_show_about)
    cmds.separator(height=6, style="none")
    cmds.showWindow(_UI_WINDOW)


# ---------- 菜单 ----------

def _menu_cb_import(*args):
    try:
        _do_import_files()
    except Exception:
        traceback.print_exc()


def _menu_cb_options(*args):
    try:
        show_ui()
    except Exception:
        traceback.print_exc()


def _menu_cb_view_xml(*args):
    try:
        _view_xml_from_last_or_prompt()
    except Exception:
        traceback.print_exc()


def _menu_cb_materials(*args):
    try:
        _show_material_dialog()
    except Exception:
        traceback.print_exc()


def _install_menu():
    if cmds.menu(_MENU_NAME, exists=True):
        cmds.deleteUI(_MENU_NAME)
    try:
        gmain = mel.eval("$temp1 = $gMainWindow")
    except Exception:
        gmain = "MayaWindow"
    cmds.menu(_MENU_NAME, label="MudRunner X", parent=gmain, tearOff=True)
    cmds.menuItem(label="Import X File...", command=_menu_cb_options)
    cmds.menuItem(divider=True)
    cmds.menuItem(label="View / Reimport Material XML...",
                  command=_menu_cb_materials)
    cmds.menuItem(label="View Bone Bindings (last import / from X file)...",
                  command=_menu_cb_bone_bindings)
    cmds.menuItem(divider=True)
    cmds.menuItem(label="About MudRunner X Importer...",
                  command=_show_about)


def _remove_menu():
    if cmds.menu(_MENU_NAME, exists=True):
        try:
            cmds.deleteUI(_MENU_NAME)
        except Exception:
            pass


# ===========================================================================
# Section 6: Plugin entry
# ===========================================================================

def _cmd_import(path, flip_axis='Z', flip_v=True, anim_scale=None,
                tex_dir=None, import_collision=False, import_socketpoints=True):
    return import_x_file(path, flip_axis, flip_v, anim_scale,
                         tex_dir=tex_dir or _load_tex_dir(),
                         import_collision=import_collision,
                         import_socketpoints=import_socketpoints)


def _try_register_translator():
    try:
        plugin = OpenMayaMPx.MFnPlugin()
        plugin.registerFileTranslator(
            kTranslatorName, "", create_translator, "", kDefaultOptions)
        print('[xfile_importer] Translator "%s" registered.'
              % kTranslatorName)
        return True
    except Exception as e:
        print('[xfile_importer] WARNING: could not register translator: %r'
              % e)
        print('[xfile_importer] File > Import 不可用；请使用菜单 '
              '"DirectX → Import X File..." 或 cmds.xfileImport()')
        return False


def initializePlugin(mobject):
    try:
        _install_menu()
    except Exception:
        traceback.print_exc()

    cmds.xfileImport = _cmd_import
    cmds.xfileImportOptions = show_ui

    _try_register_translator()

    print('[xfile_importer] Plugin loaded '
          '(MudRunner UI / DirectX menu installed) '
          '【无蒙皮版本（保留骨骼）· 性能优化版】.')


def uninitializePlugin(mobject):
    try:
        _remove_menu()
    except Exception:
        traceback.print_exc()

    try:
        plugin = OpenMayaMPx.MFnPlugin()
        plugin.deregisterFileTranslator(kTranslatorName)
    except Exception:
        pass

    for name in ('xfileImport', 'xfileImportOptions'):
        if hasattr(cmds, name):
            try:
                delattr(cmds, name)
            except AttributeError:
                pass
    print('[xfile_importer] Plugin unloaded.')


if __name__ == "__main__":
    show_ui()