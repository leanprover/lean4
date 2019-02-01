// Lean compiler output
// Module: init.control.id
// Imports: init.control.lift
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s2_id_s4_bind_s6___rarg(obj*, obj*);
obj* _l_s2_id_s10_monad__run;
obj* _l_s2_id_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s2_id_s5_monad;
obj* _l_s2_id_s3_run_s6___rarg(obj*);
obj* _l_s2_id_s3_run(obj*);
obj* _l_s2_id_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s2_id(obj*);
obj* _l_s2_id_s4_bind(obj*, obj*);
obj* _l_s2_id_s4_bind_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* _l_s2_id_s4_bind(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind_s6___rarg), 2, 0);
return x_4;
}
}
obj* _init__l_s2_id_s5_monad() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s2_id_s5_monad_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::apply_1(x_2, x_3);
return x_6;
}
}
obj* _l_s2_id_s5_monad_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _l_s2_id_s5_monad_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_3;
}
}
obj* _l_s2_id_s3_run_s6___rarg(obj* x_0) {
{

return x_0;
}
}
obj* _l_s2_id_s3_run(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s3_run_s6___rarg), 1, 0);
return x_2;
}
}
obj* _init__l_s2_id_s10_monad__run() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s3_run), 1, 0);
return x_0;
}
}
void _l_initialize__l_s4_init_s7_control_s4_lift();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s2_id() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s4_lift();
 _l_s2_id_s5_monad = _init__l_s2_id_s5_monad();
 _l_s2_id_s10_monad__run = _init__l_s2_id_s10_monad__run();
}
