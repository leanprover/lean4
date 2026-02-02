// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Power
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Simproc import Lean.Meta.NatInstTesters
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pow_add_congr"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 167, 3, 17, 68, 5, 224, 21)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_st_ref_get(x_7);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
lean_inc(x_19);
x_21 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_19, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
lean_dec(x_22);
lean_inc_ref(x_23);
x_25 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_23, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_37; lean_object* x_42; uint8_t x_43; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
x_42 = l_Lean_Expr_cleanupAnnotations(x_26);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_42);
lean_dec_ref(x_23);
x_44 = lean_box(0);
x_45 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_45;
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_46);
x_47 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_49 = lean_box(0);
x_50 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_50;
goto block_41;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_47);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_54 = lean_box(0);
x_55 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_54, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_55;
goto block_41;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_56);
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_59 = lean_box(0);
x_60 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_59, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_60;
goto block_41;
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_112; uint8_t x_113; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_61);
x_112 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_113 = l_Lean_Expr_isApp(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_112);
lean_dec_ref(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_114 = lean_box(0);
x_115 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_114, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_115;
goto block_41;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_116);
x_117 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_118 = l_Lean_Expr_isApp(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_119 = lean_box(0);
x_120 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_120;
goto block_41;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_121);
x_122 = l_Lean_Expr_appFnCleanup___redArg(x_117);
x_123 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8));
x_124 = l_Lean_Expr_isConstOf(x_122, x_123);
lean_dec_ref(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_121);
lean_dec_ref(x_116);
lean_dec_ref(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_125 = lean_box(0);
x_126 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_125, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = x_126;
goto block_41;
}
else
{
uint8_t x_127; 
x_127 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_121);
lean_dec_ref(x_121);
if (x_127 == 0)
{
lean_dec_ref(x_116);
x_62 = x_127;
goto block_111;
}
else
{
uint8_t x_128; 
x_128 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_116);
lean_dec_ref(x_116);
x_62 = x_128;
goto block_111;
}
}
}
}
block_111:
{
if (x_62 == 0)
{
lean_dec_ref(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_29 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_63; 
x_63 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_61);
lean_dec_ref(x_61);
if (x_63 == 0)
{
lean_dec_ref(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_29 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_56, x_14);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_29 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Lean_Expr_appFn_x21(x_3);
x_68 = l_Lean_Expr_appFn_x21(x_67);
lean_dec_ref(x_67);
lean_inc_ref(x_51);
lean_inc_ref(x_4);
lean_inc_ref(x_68);
x_69 = l_Lean_mkAppB(x_68, x_4, x_51);
lean_inc_ref(x_46);
lean_inc_ref(x_4);
x_70 = l_Lean_mkAppB(x_68, x_4, x_46);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_71 = l_Lean_Meta_mkMul(x_69, x_70, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_73 = lean_grind_preprocess(x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_77);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_77);
x_78 = lean_grind_internalize(x_77, x_76, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_78);
x_79 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5));
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
x_80 = l_Lean_Meta_Grind_Arith_mkSemiringThm(x_79, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_1);
x_83 = lean_grind_mk_eq_proof(x_1, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_85 = l_Lean_Meta_Simp_Result_getProof(x_74, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
lean_inc_ref(x_1);
lean_inc_ref(x_77);
lean_inc_ref(x_4);
x_87 = l_Lean_mkApp7(x_82, x_4, x_77, x_1, x_51, x_46, x_84, x_86);
x_88 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_3);
x_89 = l_Lean_Meta_Grind_pushEqCore___redArg(x_3, x_77, x_87, x_88, x_7, x_9, x_13, x_14, x_15, x_16);
x_37 = x_89;
goto block_41;
}
else
{
uint8_t x_90; 
lean_dec(x_84);
lean_dec(x_82);
lean_dec_ref(x_77);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_82);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_83);
if (x_93 == 0)
{
return x_83;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
lean_dec(x_83);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
lean_dec(x_81);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_29 = lean_box(0);
goto block_36;
}
}
else
{
uint8_t x_96; 
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_80);
if (x_96 == 0)
{
return x_80;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
lean_dec(x_80);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec_ref(x_23);
x_37 = x_78;
goto block_41;
}
}
else
{
uint8_t x_99; 
lean_dec(x_74);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_75);
if (x_99 == 0)
{
return x_75;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_75, 0);
lean_inc(x_100);
lean_dec(x_75);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_73);
if (x_102 == 0)
{
return x_73;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_73, 0);
lean_inc(x_103);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_71);
if (x_105 == 0)
{
return x_71;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_71, 0);
lean_inc(x_106);
lean_dec(x_71);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_108 = !lean_is_exclusive(x_64);
if (x_108 == 0)
{
return x_64;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_64, 0);
lean_inc(x_109);
lean_dec(x_64);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
}
}
}
}
block_36:
{
uint8_t x_30; 
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_24, x_1);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_19);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_24);
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0));
if (lean_is_scalar(x_20)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_20;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_19);
if (lean_is_scalar(x_27)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_27;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
block_41:
{
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
x_29 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_129 = !lean_is_exclusive(x_25);
if (x_129 == 0)
{
return x_25;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_25, 0);
lean_inc(x_130);
lean_dec(x_25);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_132 = !lean_is_exclusive(x_21);
if (x_132 == 0)
{
return x_21;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_21, 0);
lean_inc(x_133);
lean_dec(x_21);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc_ref(x_30);
x_37 = l_Lean_Expr_cleanupAnnotations(x_30);
x_38 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_33, x_27);
lean_dec_ref(x_27);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
lean_inc_ref(x_19);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_19);
x_47 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(x_19, x_30, x_1, x_22, x_33, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_30);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec_ref(x_50);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec_ref(x_54);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
