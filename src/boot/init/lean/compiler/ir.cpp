// Lean compiler output
// Module: init.lean.compiler.ir
// Imports: init.default init.lean.name
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_ir_fid;
obj* l_lean_ir_varid;
obj* _init_l_lean_ir_varid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
void initialize_init_default();
void initialize_init_lean_name();
static bool _G_initialized = false;
void initialize_init_lean_compiler_ir() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_default();
 initialize_init_lean_name();
 l_lean_ir_varid = _init_l_lean_ir_varid();
lean::mark_persistent(l_lean_ir_varid);
 l_lean_ir_fid = _init_l_lean_ir_fid();
lean::mark_persistent(l_lean_ir_fid);
}
