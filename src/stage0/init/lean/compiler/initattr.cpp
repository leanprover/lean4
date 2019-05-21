// Lean compiler output
// Module: init.lean.compiler.initattr
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
extern "C" obj* lean_get_init_fn_name_for(obj*, obj*);
obj* l_Lean_hasInitAttr___boxed(obj*, obj*);
extern "C" uint8 lean_is_io_unit_init(obj*, obj*);
uint8 l_Lean_hasInitAttr(obj*, obj*);
obj* l_Lean_getInitFnNameFor___boxed(obj*, obj*);
obj* l_Lean_isIOUnitInitFn___boxed(obj*, obj*);
obj* l_Lean_isIOUnitInitFn___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_is_io_unit_init(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getInitFnNameFor___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_get_init_fn_name_for(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_hasInitAttr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_get_init_fn_name_for(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_hasInitAttr___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_hasInitAttr(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_initattr(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
return w;
}
