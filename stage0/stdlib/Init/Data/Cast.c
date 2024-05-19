// Lean compiler output
// Module: Init.Data.Cast
// Imports: Init.Coe
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
LEAN_EXPORT lean_object* l_Nat_cast___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instNatCastNat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast(lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast(lean_object*);
LEAN_EXPORT lean_object* l_instNatCastNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast(lean_object*);
LEAN_EXPORT lean_object* l_instNatCastNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instNatCastNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instNatCastNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_cast___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_cast___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instCoeTailNatOfNatCast___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_cast___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instCoeHTCTNatOfNatCast___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Coe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Cast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
