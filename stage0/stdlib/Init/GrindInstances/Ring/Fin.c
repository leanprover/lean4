// Lean compiler output
// Module: Init.GrindInstances.Ring.Fin
// Imports: Init.Data.Zero Init.Grind.Ring.Basic Init.GrindInstances.ToInt Init.Data.Fin.Lemmas
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
lean_object* l_Fin_neg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero(lean_object*, lean_object*);
lean_object* l_Fin_intCast___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object*, lean_object*);
lean_object* l_Fin_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero___redArg(lean_object*);
lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_mod(x_4, x_1);
x_6 = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_npowRec___redArg(x_5, x_6, x_3, x_2);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Fin_npow___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Fin_npow___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_npow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Fin_npow(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instHPowFinNatOfNeZero(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Grind_Fin_npow___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, lean_box(0));
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Fin_NatCast_instNatCast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, lean_box(0));
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Zero(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Zero(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
