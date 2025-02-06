// Lean compiler output
// Module: Init.SizeOf
// Imports: Init.Tactics
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_default_sizeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfDefault(lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_default_sizeOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfNat(lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfForallUnit(lean_object*);
static lean_object* l_instSizeOfDefault___closed__1;
LEAN_EXPORT lean_object* l_default_sizeOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_default_sizeOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_default_sizeOf(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_instSizeOfDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_default_sizeOf___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instSizeOfDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOfDefault___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSizeOfNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instSizeOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSizeOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSizeOfForallUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSizeOfForallUnit___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_SizeOf(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instSizeOfDefault___closed__1 = _init_l_instSizeOfDefault___closed__1();
lean_mark_persistent(l_instSizeOfDefault___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
