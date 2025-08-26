// Lean compiler output
// Module: Init.GrindInstances.Ring.BitVec
// Imports: Init.Grind.Ring.Basic Init.Grind.Ordered.Order Init.GrindInstances.ToInt Init.Data.BitVec.Basic Init.Data.BitVec.Basic Init.Grind.ToInt Init.Grind.ToInt
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
lean_object* l_BitVec_instOfNat___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_neg___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_instNatCast___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
lean_object* l_BitVec_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHPow___redArg(lean_object*);
lean_object* l_BitVec_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_BitVec_ofNat(x_1, x_2);
x_5 = l_BitVec_mul(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_BitVec_ofInt(x_1, x_2);
x_5 = l_BitVec_mul(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_instCommRingBitVec___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Grind_instCommRingBitVec___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_BitVec_instNatCast___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_BitVec_instOfNat___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_instHPow___redArg(x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_7);
lean_ctor_set(x_13, 4, x_2);
lean_ctor_set(x_13, 5, x_9);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_instCommRingBitVec___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_instCommRingBitVec___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ordered_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_BitVec(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Order(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
