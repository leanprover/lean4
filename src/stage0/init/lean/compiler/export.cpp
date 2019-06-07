// Lean compiler output
// Module: init.lean.compiler.export
// Imports: init.lean.environment
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
obj* l_Lean_getExportNameFor___boxed(obj*, obj*);
extern "C" obj* lean_get_export_name_for(obj*, obj*);
uint8 l_Lean_isExport(obj*, obj*);
obj* l_Lean_isExport___boxed(obj*, obj*);
obj* l_Lean_getExportNameFor___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_export_name_for(x_1, x_2);
return x_3;
}
}
uint8 l_Lean_isExport(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_export_name_for(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_3);
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_isExport___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isExport(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_export(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExportNameFor"), 2, l_Lean_getExportNameFor___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isExport"), 2, l_Lean_isExport___boxed);
return w;
}
