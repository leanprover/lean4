// Lean compiler output
// Module: Init.Data.Nat.Div
// Imports: Init.WF Init.WFTactics Init.Data.Nat.Basic
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
static lean_object* l_Nat_instDivNat___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instModNat;
LEAN_EXPORT lean_object* l_Nat_instDivNat;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Nat_instModNat___closed__1;
LEAN_EXPORT lean_object* l_Nat_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_instDivNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instDivNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instDivNat___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_instModNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instModNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instModNat___closed__1;
return x_1;
}
}
lean_object* initialize_Init_WF(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WFTactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Div(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instDivNat___closed__1 = _init_l_Nat_instDivNat___closed__1();
lean_mark_persistent(l_Nat_instDivNat___closed__1);
l_Nat_instDivNat = _init_l_Nat_instDivNat();
lean_mark_persistent(l_Nat_instDivNat);
l_Nat_instModNat___closed__1 = _init_l_Nat_instModNat___closed__1();
lean_mark_persistent(l_Nat_instModNat___closed__1);
l_Nat_instModNat = _init_l_Nat_instModNat();
lean_mark_persistent(l_Nat_instModNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
