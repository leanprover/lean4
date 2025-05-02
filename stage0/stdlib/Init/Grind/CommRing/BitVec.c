// Lean compiler output
// Module: Init.Grind.CommRing.BitVec
// Imports: Init.Grind.CommRing.Basic Init.Data.BitVec.Lemmas
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
lean_object* l_BitVec_ofNat___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_neg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object*);
lean_object* l_BitVec_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_pow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt___boxed(lean_object*, lean_object*);
lean_object* l_instHPow___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingBitVec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_BitVec_pow___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_7, 0, x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_BitVec_instOfNat___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_BitVec_ofNat___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_8);
lean_ctor_set(x_11, 6, x_9);
lean_ctor_set(x_11, 7, x_10);
return x_11;
}
}
lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing_BitVec(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
