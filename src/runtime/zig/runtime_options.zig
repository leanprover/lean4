// Runtime build options for the Lean Zig runtime.
//
// This module is consumed by `alloc.zig` and `init.zig` to decide whether
// the runtime allocator symbols are exported or delegated to an external
// implementation.

pub const export_allocator_symbols: bool = true;
