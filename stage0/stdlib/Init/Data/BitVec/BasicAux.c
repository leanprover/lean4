// Lean compiler output
// Module: Init.Data.BitVec.BasicAux
// Imports: Init.Data.Fin.Basic
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
LEAN_EXPORT lean_object* l_BitVec_instOfNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instAdd(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instSub(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_mod(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOfNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOfNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instOfNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_add(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_add(x_2, x_3);
x_5 = l_BitVec_ofNat(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_add(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_pow(x_4, x_1);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
x_7 = lean_nat_add(x_6, x_2);
lean_dec(x_6);
x_8 = l_BitVec_ofNat(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_sub(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instSub(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
