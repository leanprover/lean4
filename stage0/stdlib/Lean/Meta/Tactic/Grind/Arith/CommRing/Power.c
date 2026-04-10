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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 167, 3, 17, 68, 5, 224, 21)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec(v___y_16_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_b_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_238_; 
v___x_61_ = lean_st_ref_get(v___y_50_);
v_snd_62_ = lean_ctor_get(v_b_49_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_b_49_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_b_49_, 0);
lean_dec(v_unused_239_);
v___x_64_ = v_b_49_;
v_isShared_65_ = v_isSharedCheck_238_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_dec(v_b_49_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_238_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; 
lean_inc(v_snd_62_);
v___x_66_ = l_Lean_Meta_Grind_Goal_getENode(v___x_61_, v_snd_62_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_self_68_; lean_object* v_next_69_; lean_object* v___x_70_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v___x_66_);
v_self_68_ = lean_ctor_get(v_a_67_, 0);
lean_inc_ref_n(v_self_68_, 2);
v_next_69_ = lean_ctor_get(v_a_67_, 1);
lean_inc_ref(v_next_69_);
lean_dec(v_a_67_);
v___x_70_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_68_, v___y_57_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_221_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_221_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_221_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_221_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___y_90_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_75_ = lean_box(0);
v___x_99_ = l_Lean_Expr_cleanupAnnotations(v_a_71_);
v___x_100_ = l_Lean_Expr_isApp(v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec_ref(v___x_99_);
lean_dec_ref(v_self_68_);
v___x_101_ = lean_box(0);
v___x_102_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_101_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_102_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_arg_103_ = lean_ctor_get(v___x_99_, 1);
lean_inc_ref(v_arg_103_);
v___x_104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_99_);
v___x_105_ = l_Lean_Expr_isApp(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec_ref(v___x_104_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_106_ = lean_box(0);
v___x_107_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_106_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_107_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_arg_108_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_arg_108_);
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_104_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec_ref(v___x_109_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_111_ = lean_box(0);
v___x_112_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_111_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_112_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_arg_113_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_113_);
v___x_114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_115_ = l_Lean_Expr_isApp(v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec_ref(v___x_114_);
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_116_ = lean_box(0);
v___x_117_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_116_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_117_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_118_; uint8_t v___y_120_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_arg_118_ = lean_ctor_get(v___x_114_, 1);
lean_inc_ref(v_arg_118_);
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_114_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_206_ = lean_box(0);
v___x_207_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_206_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_207_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_arg_208_ = lean_ctor_get(v___x_204_, 1);
lean_inc_ref(v_arg_208_);
v___x_209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v___x_209_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_211_ = lean_box(0);
v___x_212_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_211_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_212_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_arg_213_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_arg_213_);
v___x_214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_215_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8));
v___x_216_ = l_Lean_Expr_isConstOf(v___x_214_, v___x_215_);
lean_dec_ref(v___x_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_arg_213_);
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___x_217_ = lean_box(0);
v___x_218_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(v___x_217_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_218_;
goto v___jp_89_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_45_, v_arg_213_);
lean_dec_ref(v_arg_213_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_arg_208_);
v___y_120_ = v___x_219_;
goto v___jp_119_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_45_, v_arg_208_);
lean_dec_ref(v_arg_208_);
v___y_120_ = v___x_220_;
goto v___jp_119_;
}
}
}
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_45_, v_arg_118_);
lean_dec_ref(v_arg_118_);
if (v___x_121_ == 0)
{
lean_dec_ref(v_arg_113_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_113_, v___y_57_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; uint8_t v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v___x_122_);
v___x_124_ = lean_unbox(v_a_123_);
lean_dec(v_a_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = l_Lean_Expr_appFn_x21(v_e_46_);
v___x_126_ = l_Lean_Expr_appFn_x21(v___x_125_);
lean_dec_ref(v___x_125_);
lean_inc_ref(v_arg_108_);
lean_inc_ref_n(v_a_47_, 2);
lean_inc_ref(v___x_126_);
v___x_127_ = l_Lean_mkAppB(v___x_126_, v_a_47_, v_arg_108_);
lean_inc_ref(v_arg_103_);
v___x_128_ = l_Lean_mkAppB(v___x_126_, v_a_47_, v_arg_103_);
v___x_129_ = l_Lean_Meta_mkMul(v___x_127_, v___x_128_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
lean_dec_ref(v___x_129_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_51_);
lean_inc(v___y_50_);
v___x_131_ = lean_grind_preprocess(v_a_130_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_46_, v___y_50_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v_expr_135_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref(v___x_133_);
v_expr_135_ = lean_ctor_get(v_a_132_, 0);
lean_inc_ref_n(v_expr_135_, 2);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_51_);
lean_inc(v___y_50_);
v___x_136_ = lean_grind_internalize(v_expr_135_, v_a_134_, v___x_75_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref(v___x_136_);
v___x_137_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5));
lean_inc_ref(v_a_48_);
v___x_138_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_137_, v_a_48_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
if (lean_obj_tag(v_a_139_) == 1)
{
lean_object* v_val_140_; lean_object* v___x_141_; 
v_val_140_ = lean_ctor_get(v_a_139_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_a_139_);
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_51_);
lean_inc(v___y_50_);
lean_inc_ref(v_a_44_);
v___x_141_ = lean_grind_mk_eq_proof(v_a_44_, v_self_68_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v___x_141_);
v___x_143_ = l_Lean_Meta_Simp_Result_getProof(v_a_132_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v___x_143_);
lean_inc_ref(v_a_44_);
lean_inc_ref(v_expr_135_);
lean_inc_ref(v_a_47_);
v___x_145_ = l_Lean_mkApp7(v_val_140_, v_a_47_, v_expr_135_, v_a_44_, v_arg_108_, v_arg_103_, v_a_142_, v_a_144_);
v___x_146_ = 0;
lean_inc_ref(v_e_46_);
v___x_147_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_46_, v_expr_135_, v___x_145_, v___x_146_, v___y_50_, v___y_52_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_147_;
goto v___jp_89_;
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_a_142_);
lean_dec(v_val_140_);
lean_dec_ref(v_expr_135_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_148_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_143_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_143_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_val_140_);
lean_dec_ref(v_expr_135_);
lean_dec(v_a_132_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_156_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_141_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_141_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_dec(v_a_139_);
lean_dec_ref(v_expr_135_);
lean_dec(v_a_132_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_expr_135_);
lean_dec(v_a_132_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_164_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_138_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_138_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_dec_ref(v_expr_135_);
lean_dec(v_a_132_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_dec_ref(v_self_68_);
v___y_90_ = v___x_136_;
goto v___jp_89_;
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_a_132_);
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_172_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_133_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_133_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_180_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_131_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_131_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_188_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_129_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_129_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_arg_108_);
lean_dec_ref(v_arg_103_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_196_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_122_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_122_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
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
v___jp_76_:
{
uint8_t v___x_77_; 
v___x_77_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_69_, v_a_44_);
if (v___x_77_ == 0)
{
lean_object* v___x_79_; 
lean_del_object(v___x_73_);
lean_dec(v_snd_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v_next_69_);
lean_ctor_set(v___x_64_, 0, v___x_75_);
v___x_79_ = v___x_64_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_next_69_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
v_b_49_ = v___x_79_;
goto _start;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec_ref(v_next_69_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v___x_82_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0));
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_82_);
v___x_84_ = v___x_64_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_snd_62_);
v___x_84_ = v_reuseFailAlloc_88_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_86_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_84_);
v___x_86_ = v___x_73_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
v___jp_89_:
{
if (lean_obj_tag(v___y_90_) == 0)
{
lean_dec_ref(v___y_90_);
goto v___jp_76_;
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_91_ = lean_ctor_get(v___y_90_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___y_90_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___y_90_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___y_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_222_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_70_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_70_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_230_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_66_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_66_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args){
lean_object* v_a_240_ = _args[0];
lean_object* v_a_241_ = _args[1];
lean_object* v_e_242_ = _args[2];
lean_object* v_a_243_ = _args[3];
lean_object* v_a_244_ = _args[4];
lean_object* v_b_245_ = _args[5];
lean_object* v___y_246_ = _args[6];
lean_object* v___y_247_ = _args[7];
lean_object* v___y_248_ = _args[8];
lean_object* v___y_249_ = _args[9];
lean_object* v___y_250_ = _args[10];
lean_object* v___y_251_ = _args[11];
lean_object* v___y_252_ = _args[12];
lean_object* v___y_253_ = _args[13];
lean_object* v___y_254_ = _args[14];
lean_object* v___y_255_ = _args[15];
lean_object* v___y_256_ = _args[16];
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_240_, v_a_241_, v_e_242_, v_a_243_, v_a_244_, v_b_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v_a_241_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
lean_inc_ref(v_e_266_);
v___x_281_ = l_Lean_Expr_cleanupAnnotations(v_e_266_);
v___x_282_ = l_Lean_Expr_isApp(v___x_281_);
if (v___x_282_ == 0)
{
lean_dec_ref(v___x_281_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_arg_283_ = lean_ctor_get(v___x_281_, 1);
lean_inc_ref(v_arg_283_);
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_281_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v___x_284_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_arg_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc_ref(v_arg_286_);
v___x_287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
v___x_288_ = l_Lean_Expr_isApp(v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = l_Lean_Expr_appFnCleanup___redArg(v___x_287_);
v___x_290_ = l_Lean_Expr_isApp(v___x_289_);
if (v___x_290_ == 0)
{
lean_dec_ref(v___x_289_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_arg_291_ = lean_ctor_get(v___x_289_, 1);
lean_inc_ref(v_arg_291_);
v___x_292_ = l_Lean_Expr_appFnCleanup___redArg(v___x_289_);
v___x_293_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v___x_292_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_arg_294_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_294_);
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_arg_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref(v_arg_297_);
v___x_298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_300_ = l_Lean_Expr_isConstOf(v___x_298_, v___x_299_);
lean_dec_ref(v___x_298_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
goto v___jp_278_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_inc_ref(v_arg_294_);
v___x_301_ = l_Lean_Expr_cleanupAnnotations(v_arg_294_);
v___x_302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_302_);
lean_dec_ref(v___x_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_297_, v_arg_291_);
lean_dec_ref(v_arg_291_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_294_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_e_266_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
lean_inc_ref(v_arg_283_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_arg_283_);
v___x_311_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_arg_283_, v_arg_294_, v_e_266_, v_arg_286_, v_arg_297_, v___x_310_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_arg_294_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_325_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_325_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_fst_316_; 
v_fst_316_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_fst_316_);
lean_dec(v_a_312_);
if (lean_obj_tag(v_fst_316_) == 0)
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v_val_321_; lean_object* v___x_323_; 
v_val_321_ = lean_ctor_get(v_fst_316_, 0);
lean_inc(v_val_321_);
lean_dec_ref(v_fst_316_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_val_321_);
v___x_323_ = v___x_314_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_val_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_311_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_311_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
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
v___jp_278_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec(v_a_335_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
v___x_350_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
return v_res_352_;
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
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
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
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
}
#ifdef __cplusplus
}
#endif
