// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Power
// Imports: import Init.Grind import Lean.Meta.Tactic.Grind.Arith.Simproc import Lean.Meta.NatInstTesters public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_195; 
x_18 = lean_st_ref_get(x_7);
x_19 = lean_ctor_get(x_6, 1);
x_195 = !lean_is_exclusive(x_6);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_6, 0);
lean_dec(x_196);
x_20 = x_6;
x_21 = x_195;
goto block_194;
}
else
{
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_22; 
lean_inc(x_19);
x_22 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_19, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
lean_dec(x_23);
lean_inc_ref(x_24);
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_24, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_177; 
x_27 = lean_ctor_get(x_26, 0);
x_177 = !lean_is_exclusive(x_26);
if (x_177 == 0)
{
x_28 = x_26;
x_29 = x_177;
goto block_176;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_30; lean_object* x_44; lean_object* x_54; uint8_t x_55; 
x_30 = lean_box(0);
x_54 = l_Lean_Expr_cleanupAnnotations(x_27);
x_55 = l_Lean_Expr_isApp(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_54);
lean_dec_ref(x_24);
x_56 = lean_box(0);
x_57 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_56, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_57;
goto block_53;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_58);
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_54);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_61 = lean_box(0);
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_62;
goto block_53;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_63);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_66 = lean_box(0);
x_67 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_67;
goto block_53;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_68);
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_71 = lean_box(0);
x_72 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_71, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_72;
goto block_53;
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_159; uint8_t x_160; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_73);
x_159 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_160 = l_Lean_Expr_isApp(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_159);
lean_dec_ref(x_73);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_161 = lean_box(0);
x_162 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_161, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_162;
goto block_53;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_159, 1);
lean_inc_ref(x_163);
x_164 = l_Lean_Expr_appFnCleanup___redArg(x_159);
x_165 = l_Lean_Expr_isApp(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec_ref(x_73);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_166 = lean_box(0);
x_167 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_166, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_167;
goto block_53;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_164, 1);
lean_inc_ref(x_168);
x_169 = l_Lean_Expr_appFnCleanup___redArg(x_164);
x_170 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8));
x_171 = l_Lean_Expr_isConstOf(x_169, x_170);
lean_dec_ref(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_168);
lean_dec_ref(x_163);
lean_dec_ref(x_73);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_172 = lean_box(0);
x_173 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_44 = x_173;
goto block_53;
}
else
{
uint8_t x_174; 
x_174 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_168);
lean_dec_ref(x_168);
if (x_174 == 0)
{
lean_dec_ref(x_163);
x_74 = x_174;
goto block_158;
}
else
{
uint8_t x_175; 
x_175 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_163);
lean_dec_ref(x_163);
x_74 = x_175;
goto block_158;
}
}
}
}
block_158:
{
if (x_74 == 0)
{
lean_dec_ref(x_73);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
goto block_43;
}
else
{
uint8_t x_75; 
x_75 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_73);
lean_dec_ref(x_73);
if (x_75 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
goto block_43;
}
else
{
lean_object* x_76; 
x_76 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_68, x_14);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = l_Lean_Expr_appFn_x21(x_3);
x_80 = l_Lean_Expr_appFn_x21(x_79);
lean_dec_ref(x_79);
lean_inc_ref(x_63);
lean_inc_ref(x_4);
lean_inc_ref(x_80);
x_81 = l_Lean_mkAppB(x_80, x_4, x_63);
lean_inc_ref(x_58);
lean_inc_ref(x_4);
x_82 = l_Lean_mkAppB(x_80, x_4, x_58);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_83 = l_Lean_Meta_mkMul(x_81, x_82, x_13, x_14, x_15, x_16);
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
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_85 = lean_grind_preprocess(x_84, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_89);
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
lean_inc_ref(x_89);
x_90 = lean_grind_internalize(x_89, x_88, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_90);
x_91 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5));
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
x_92 = l_Lean_Meta_Grind_Arith_mkSemiringThm(x_91, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
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
x_95 = lean_grind_mk_eq_proof(x_1, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_97 = l_Lean_Meta_Simp_Result_getProof(x_86, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc_ref(x_1);
lean_inc_ref(x_89);
lean_inc_ref(x_4);
x_99 = l_Lean_mkApp7(x_94, x_4, x_89, x_1, x_63, x_58, x_96, x_98);
x_100 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_3);
x_101 = l_Lean_Meta_Grind_pushEqCore___redArg(x_3, x_89, x_99, x_100, x_7, x_9, x_13, x_14, x_15, x_16);
x_44 = x_101;
goto block_53;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec_ref(x_89);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
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
x_102 = lean_ctor_get(x_97, 0);
x_109 = !lean_is_exclusive(x_97);
if (x_109 == 0)
{
x_103 = x_97;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_94);
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
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
x_110 = lean_ctor_get(x_95, 0);
x_117 = !lean_is_exclusive(x_95);
if (x_117 == 0)
{
x_111 = x_95;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_95);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
else
{
lean_dec(x_93);
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
goto block_43;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_118 = lean_ctor_get(x_92, 0);
x_125 = !lean_is_exclusive(x_92);
if (x_125 == 0)
{
x_119 = x_92;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_92);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_44 = x_90;
goto block_53;
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_126 = lean_ctor_get(x_87, 0);
x_133 = !lean_is_exclusive(x_87);
if (x_133 == 0)
{
x_127 = x_87;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_87);
x_127 = lean_box(0);
x_128 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_129; 
if (x_128 == 0)
{
x_129 = x_127;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_141; 
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_134 = lean_ctor_get(x_85, 0);
x_141 = !lean_is_exclusive(x_85);
if (x_141 == 0)
{
x_135 = x_85;
x_136 = x_141;
goto block_140;
}
else
{
lean_inc(x_134);
lean_dec(x_85);
x_135 = lean_box(0);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_136 == 0)
{
x_137 = x_135;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_134);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_149; 
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_142 = lean_ctor_get(x_83, 0);
x_149 = !lean_is_exclusive(x_83);
if (x_149 == 0)
{
x_143 = x_83;
x_144 = x_149;
goto block_148;
}
else
{
lean_inc(x_142);
lean_dec(x_83);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
lean_dec_ref(x_63);
lean_dec_ref(x_58);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_150 = lean_ctor_get(x_76, 0);
x_157 = !lean_is_exclusive(x_76);
if (x_157 == 0)
{
x_151 = x_76;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_76);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
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
block_43:
{
uint8_t x_31; 
x_31 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_25, x_1);
if (x_31 == 0)
{
lean_object* x_32; 
lean_del_object(x_28);
lean_dec(x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_30);
x_32 = x_20;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_25);
x_32 = x_35;
goto block_34;
}
block_34:
{
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_25);
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
x_36 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_36);
x_37 = x_20;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_19);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_37);
x_38 = x_28;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
block_53:
{
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
goto block_43;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
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
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
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
x_178 = lean_ctor_get(x_26, 0);
x_185 = !lean_is_exclusive(x_26);
if (x_185 == 0)
{
x_179 = x_26;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_26);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_193; 
lean_del_object(x_20);
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
x_186 = lean_ctor_get(x_22, 0);
x_193 = !lean_is_exclusive(x_22);
if (x_193 == 0)
{
x_187 = x_22;
x_188 = x_193;
goto block_192;
}
else
{
lean_inc(x_186);
lean_dec(x_22);
x_187 = lean_box(0);
x_188 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_189; 
if (x_188 == 0)
{
x_189 = x_187;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_186);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
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
lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_1);
x_16 = l_Lean_Expr_cleanupAnnotations(x_1);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
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
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
goto block_15;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_29);
x_36 = l_Lean_Expr_cleanupAnnotations(x_29);
x_37 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_32);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_32, x_26);
lean_dec_ref(x_26);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_32);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
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
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box(0);
lean_inc_ref(x_18);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_18);
x_46 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(x_18, x_29, x_1, x_21, x_32, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_29);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_60; 
x_47 = lean_ctor_get(x_46, 0);
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
x_48 = x_46;
x_49 = x_60;
goto block_59;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_51);
x_52 = x_48;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec_ref(x_50);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_55);
x_56 = x_48;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
x_61 = lean_ctor_get(x_46, 0);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
x_62 = x_46;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
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
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
}
#ifdef __cplusplus
}
#endif
