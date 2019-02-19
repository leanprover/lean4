// Lean compiler output
// Module: init.control.monad_fail
// Imports: init.control.lift init.data.string.basic
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
obj* l_monad__fail__lift(obj*, obj*);
obj* l_monad__fail__lift___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_match__failed___rarg(obj*);
obj* l_match__failed(obj*, obj*);
obj* l_match__failed___rarg___closed__1;
obj* _init_l_match__failed___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("match failed");
return x_0;
}
}
obj* l_match__failed___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_match__failed___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_match__failed(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_match__failed___rarg), 1, 0);
return x_4;
}
}
obj* l_monad__fail__lift___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::apply_2(x_1, lean::box(0), x_4);
x_8 = lean::apply_2(x_0, lean::box(0), x_7);
return x_8;
}
}
obj* l_monad__fail__lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__fail__lift___rarg), 5, 0);
return x_4;
}
}
void initialize_init_control_lift();
void initialize_init_data_string_basic();
static bool _G_initialized = false;
void initialize_init_control_monad__fail() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_lift();
 initialize_init_data_string_basic();
 l_match__failed___rarg___closed__1 = _init_l_match__failed___rarg___closed__1();
lean::mark_persistent(l_match__failed___rarg___closed__1);
}
