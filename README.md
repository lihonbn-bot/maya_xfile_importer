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
使用：菜单栏 → Mudrunner X → Import X File...

<img width="461" height="368" alt="image" src="https://github.com/user-attachments/assets/a06f2912-265c-401a-988b-af3906c80425" />

