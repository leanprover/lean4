// Lean compiler output
// Module: init.lean.runtime
// Imports: init.core
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
obj* l_Lean_maxSmallNatFn___boxed(obj*);
extern "C" obj* lean_closure_max_args(obj*);
extern "C" obj* lean_max_small_nat(obj*);
obj* l_Lean_closureMaxArgs;
obj* l_Lean_maxSmallNat;
obj* l_Lean_closureMaxArgsFn___boxed(obj*);
obj* l_Lean_closureMaxArgsFn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_closure_max_args(x_0);
return x_1;
}
}
obj* l_Lean_maxSmallNatFn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_max_small_nat(x_0);
return x_1;
}
}
obj* _init_l_Lean_closureMaxArgs() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_closure_max_args(x_0);
return x_1;
}
}
obj* _init_l_Lean_maxSmallNat() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_max_small_nat(x_0);
return x_1;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_runtime(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
 l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
lean::mark_persistent(l_Lean_closureMaxArgs);
 l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
lean::mark_persistent(l_Lean_maxSmallNat);
return w;
}
