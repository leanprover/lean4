# 项目状态总览（中文）

> 本文是快速把握全局用的中文摘要；正式文档以英文为准
>（[README](../README.md)、[AGENTS.md](../AGENTS.md)、[ROADMAP](ROADMAP.md)）。

## 这个项目是什么

用 Zig 重写 Lean 4 编译器后端，作为 lean4 仓库内的影子目录（`zig-backend/`，
独立 git 仓库）开发，分两条主线：

1. **运行时**（`src/runtime/`，约 1.24 万行 Zig）：对 C++ 运行时的 ABI 兼容
   替代品。Lean 编译出的 C 代码不需要任何修改即可链接 Zig 运行时。
2. **代码生成器**（`src/EmitZig/`，约 1400 行 Lean）：`EmitZig`，把 LCNF
   直接生成 Zig 代码（替代 `EmitC.lean` 生成 C 的路径），结构上刻意镜像
   上游 EmitC，便于将来合入主树。

## 里程碑进度（截至 2026-06）

| 里程碑 | 内容 | 状态 |
| --- | --- | --- |
| M1 | 基础设施：commit 扫描/回放工具、构建骨架 | 完成 |
| M2 | ABI 兼容运行时 PoC：对象模型、引用计数、分配器、闭包、字符串、数组、双归档链接、端到端冒烟 | 完成 |
| M3 | 分配器符号回收、委托家族清理 | 完成 |
| M4/M4b | 大数：GMP 绑定、Nat/Int 算术、GMP 差分测试 | 完成 |
| M5/M5b | 任务系统：task manager、promise、取消、TLS 边界、调度器差分 | 完成 |
| M6 | EmitZig 影子后端，冒烟程序与 EmitC 输出逐字节一致 | 完成 |
| M7–M9 | 扩大 EmitZig 覆盖 → 补齐运行时缺口 → 升格进上游 | 见 [ROADMAP](ROADMAP.md) |

## 架构一句话

`zig build` 产出两个静态库，合起来替代上游单体 `libleanrt.a`：
`libleanrt-zig.a`（Zig 已接管的部分）+ `libleanrt_cpp_partial.a`
（仍委托给上游 C++ 的部分，由 CMake 构建并隐藏 Zig 已接管的符号）。
`tools/check-symbols.sh` 验证两者并集覆盖 `lean.h` 全部必需导出符号。

## 常用命令

```bash
zig build              # 构建运行时
zig build test         # 单元测试（不需要 stage1）
zig build test-all     # 全套测试（单元 + ABI + 链接 + 各差分套件）
./tools/check-symbols.sh
```

路径都可配置（构建选项 → 环境变量 → 默认值）：`LEAN4_DIR`（默认
zig-backend 的上级目录）、`GMP_PREFIX`、`LIBUV_PREFIX`（默认 homebrew）。

## 当前最重要的缺口（详见 ROADMAP）

1. **EmitZig 还不能编译大块 stdlib**：缺闭项常量池（`emitGroundDecl`），
   8 处 panic 占位（multi-inc/dec、opaque extern 等）。→ M7
2. **混合链接下的分配器崩溃**：与真 mimalloc 共存时 `freeLegacySmall`
   会段错误，`scheduler-diff` 因此暂时损坏并被排除出 test-all。→ M8
3. **运行时尚有 unimplemented 桩**：部分 string/debug/io 函数被调用即
   panic。→ M8
