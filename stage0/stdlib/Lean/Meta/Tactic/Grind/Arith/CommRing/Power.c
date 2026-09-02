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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pow_add_congr"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(66, 167, 3, 17, 68, 5, 224, 21)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_242_; 
v___x_61_ = lean_st_ref_get(v___y_50_);
v_snd_62_ = lean_ctor_get(v_a_49_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_a_49_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_a_49_, 0);
lean_dec(v_unused_243_);
v___x_64_ = v_a_49_;
v_isShared_65_ = v_isSharedCheck_242_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_dec(v_a_49_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_242_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; 
lean_inc(v_snd_62_);
v___x_66_ = l_Lean_Meta_Grind_Goal_getENode(v___x_61_, v_snd_62_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___x_61_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_self_68_; lean_object* v_next_69_; lean_object* v___x_70_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v_self_68_ = lean_ctor_get(v_a_67_, 0);
lean_inc_ref_n(v_self_68_, 2);
v_next_69_ = lean_ctor_get(v_a_67_, 1);
lean_inc_ref(v_next_69_);
lean_dec(v_a_67_);
v___x_70_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_68_, v___y_57_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_225_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_225_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_225_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_225_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___y_92_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_75_ = lean_box(0);
v___x_101_ = l_Lean_Expr_cleanupAnnotations(v_a_71_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_68_);
v___x_103_ = lean_box(0);
v___x_104_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_103_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_105_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_105_);
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_107_ = l_Lean_Expr_isApp(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec_ref(v___x_106_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_108_ = lean_box(0);
v___x_109_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_108_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_arg_110_ = lean_ctor_get(v___x_106_, 1);
lean_inc_ref(v_arg_110_);
v___x_111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_106_);
v___x_112_ = l_Lean_Expr_isApp(v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec_ref(v___x_111_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_113_ = lean_box(0);
v___x_114_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_113_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_114_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_arg_115_ = lean_ctor_get(v___x_111_, 1);
lean_inc_ref(v_arg_115_);
v___x_116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_111_);
v___x_117_ = l_Lean_Expr_isApp(v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec_ref(v___x_116_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_118_ = lean_box(0);
v___x_119_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_118_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_119_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_arg_120_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_arg_120_);
v___x_121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_116_);
v___x_122_ = l_Lean_Expr_isApp(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v_arg_120_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_123_ = lean_box(0);
v___x_124_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_123_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_124_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_125_ = lean_ctor_get(v___x_121_, 1);
lean_inc_ref(v_arg_125_);
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_121_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_120_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_128_ = lean_box(0);
v___x_129_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_128_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_129_;
goto v___jp_91_;
}
else
{
lean_object* v_arg_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_arg_130_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_arg_130_);
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_132_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3));
v___x_133_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_132_);
lean_dec_ref(v___x_131_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_120_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___x_134_ = lean_box(0);
v___x_135_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_134_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_135_;
goto v___jp_91_;
}
else
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_ptr_addr(v_a_45_);
v___x_137_ = lean_ptr_addr(v_arg_130_);
lean_dec_ref(v_arg_130_);
v___x_138_ = lean_usize_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_120_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
size_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_ptr_addr(v_arg_125_);
lean_dec_ref(v_arg_125_);
v___x_140_ = lean_usize_dec_eq(v___x_136_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v_arg_120_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
size_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_ptr_addr(v_arg_120_);
lean_dec_ref(v_arg_120_);
v___x_142_ = lean_usize_dec_eq(v___x_136_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_115_, v___y_57_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; uint8_t v___x_145_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_143_, 1);
v___x_145_ = lean_unbox(v_a_144_);
lean_dec(v_a_144_);
if (v___x_145_ == 0)
{
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = l_Lean_Expr_appFn_x21(v_e_46_);
v___x_147_ = l_Lean_Expr_appFn_x21(v___x_146_);
lean_dec_ref(v___x_146_);
lean_inc_ref(v_arg_110_);
lean_inc_ref_n(v_a_47_, 2);
lean_inc_ref(v___x_147_);
v___x_148_ = l_Lean_mkAppB(v___x_147_, v_a_47_, v_arg_110_);
lean_inc_ref(v_arg_105_);
v___x_149_ = l_Lean_mkAppB(v___x_147_, v_a_47_, v_arg_105_);
v___x_150_ = l_Lean_Meta_mkMul(v___x_148_, v___x_149_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
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
v___x_152_ = lean_grind_preprocess(v_a_151_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
v___x_154_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_46_, v___y_50_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v_expr_156_; lean_object* v___x_157_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v_expr_156_ = lean_ctor_get(v_a_153_, 0);
lean_inc_ref_n(v_expr_156_, 2);
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
v___x_157_ = lean_grind_internalize(v_expr_156_, v_a_155_, v___x_75_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec_ref_known(v___x_157_, 1);
v___x_158_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8));
lean_inc_ref(v_a_48_);
v___x_159_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_158_, v_a_48_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
if (lean_obj_tag(v_a_160_) == 1)
{
lean_object* v_val_161_; lean_object* v___x_162_; 
v_val_161_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v_a_160_, 1);
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
v___x_162_ = lean_grind_mk_eq_proof(v_a_44_, v_self_68_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = l_Lean_Meta_Simp_Result_getProof(v_a_153_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
lean_inc_ref(v_a_44_);
lean_inc_ref(v_expr_156_);
lean_inc_ref(v_a_47_);
v___x_166_ = l_Lean_mkApp7(v_val_161_, v_a_47_, v_expr_156_, v_a_44_, v_arg_110_, v_arg_105_, v_a_163_, v_a_165_);
v___x_167_ = 0;
lean_inc_ref(v_e_46_);
v___x_168_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_46_, v_expr_156_, v___x_166_, v___x_167_, v___y_50_, v___y_52_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_92_ = v___x_168_;
goto v___jp_91_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_a_163_);
lean_dec(v_val_161_);
lean_dec_ref(v_expr_156_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_169_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_164_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_164_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_val_161_);
lean_dec_ref(v_expr_156_);
lean_dec(v_a_153_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_177_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_162_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_162_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_dec(v_a_160_);
lean_dec_ref(v_expr_156_);
lean_dec(v_a_153_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
goto v___jp_76_;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_expr_156_);
lean_dec(v_a_153_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_185_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_159_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_159_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_dec_ref(v_expr_156_);
lean_dec(v_a_153_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_self_68_);
v___y_92_ = v___x_157_;
goto v___jp_91_;
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_a_153_);
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_193_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_154_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_154_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_201_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_152_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_152_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_209_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_150_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_150_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_arg_110_);
lean_dec_ref(v_arg_105_);
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_217_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_143_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_143_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
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
}
v___jp_76_:
{
size_t v___x_77_; size_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_ptr_addr(v_next_69_);
v___x_78_ = lean_ptr_addr(v_a_44_);
v___x_79_ = lean_usize_dec_eq(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; 
lean_del_object(v___x_73_);
lean_dec(v_snd_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v_next_69_);
lean_ctor_set(v___x_64_, 0, v___x_75_);
v___x_81_ = v___x_64_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_next_69_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v_a_49_ = v___x_81_;
goto _start;
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_86_; 
lean_dec_ref(v_next_69_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v___x_84_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0));
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_84_);
v___x_86_ = v___x_64_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_snd_62_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_88_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_86_);
v___x_88_ = v___x_73_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
v___jp_91_:
{
if (lean_obj_tag(v___y_92_) == 0)
{
lean_dec_ref_known(v___y_92_, 1);
goto v___jp_76_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_del_object(v___x_73_);
lean_dec_ref(v_next_69_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_93_ = lean_ctor_get(v___y_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___y_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___y_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___y_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_next_69_);
lean_dec_ref(v_self_68_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_226_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_70_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_70_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_234_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_66_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_66_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_a_244_ = _args[0];
lean_object* v_a_245_ = _args[1];
lean_object* v_e_246_ = _args[2];
lean_object* v_a_247_ = _args[3];
lean_object* v_a_248_ = _args[4];
lean_object* v_a_249_ = _args[5];
lean_object* v___y_250_ = _args[6];
lean_object* v___y_251_ = _args[7];
lean_object* v___y_252_ = _args[8];
lean_object* v___y_253_ = _args[9];
lean_object* v___y_254_ = _args[10];
lean_object* v___y_255_ = _args[11];
lean_object* v___y_256_ = _args[12];
lean_object* v___y_257_ = _args[13];
lean_object* v___y_258_ = _args[14];
lean_object* v___y_259_ = _args[15];
lean_object* v___y_260_ = _args[16];
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_244_, v_a_245_, v_e_246_, v_a_247_, v_a_248_, v_a_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v_a_245_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* v_e_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
lean_inc_ref(v_e_270_);
v___x_285_ = l_Lean_Expr_cleanupAnnotations(v_e_270_);
v___x_286_ = l_Lean_Expr_isApp(v___x_285_);
if (v___x_286_ == 0)
{
lean_dec_ref(v___x_285_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v_arg_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_arg_287_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_arg_287_);
v___x_288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_285_);
v___x_289_ = l_Lean_Expr_isApp(v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v___x_288_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v_arg_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_arg_290_ = lean_ctor_get(v___x_288_, 1);
lean_inc_ref(v_arg_290_);
v___x_291_ = l_Lean_Expr_appFnCleanup___redArg(v___x_288_);
v___x_292_ = l_Lean_Expr_isApp(v___x_291_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_291_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = l_Lean_Expr_appFnCleanup___redArg(v___x_291_);
v___x_294_ = l_Lean_Expr_isApp(v___x_293_);
if (v___x_294_ == 0)
{
lean_dec_ref(v___x_293_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v_arg_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_arg_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc_ref(v_arg_295_);
v___x_296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_293_);
v___x_297_ = l_Lean_Expr_isApp(v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v___x_296_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v_arg_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_arg_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc_ref(v_arg_298_);
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_296_);
v___x_300_ = l_Lean_Expr_isApp(v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v___x_299_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v_arg_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_arg_301_ = lean_ctor_get(v___x_299_, 1);
lean_inc_ref(v_arg_301_);
v___x_302_ = l_Lean_Expr_appFnCleanup___redArg(v___x_299_);
v___x_303_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_304_ = l_Lean_Expr_isConstOf(v___x_302_, v___x_303_);
lean_dec_ref(v___x_302_);
if (v___x_304_ == 0)
{
lean_dec_ref(v_arg_301_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
goto v___jp_282_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
lean_inc_ref(v_arg_298_);
v___x_305_ = l_Lean_Expr_cleanupAnnotations(v_arg_298_);
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_305_, v___x_306_);
lean_dec_ref(v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref(v_arg_301_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v_arg_295_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
size_t v___x_310_; size_t v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_ptr_addr(v_arg_301_);
v___x_311_ = lean_ptr_addr(v_arg_295_);
lean_dec_ref(v_arg_295_);
v___x_312_ = lean_usize_dec_eq(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v_arg_301_);
lean_dec_ref(v_arg_298_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_287_);
lean_dec_ref(v_e_270_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
lean_inc_ref(v_arg_287_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_arg_287_);
v___x_317_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_arg_287_, v_arg_298_, v_e_270_, v_arg_290_, v_arg_301_, v___x_316_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec_ref(v_arg_298_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_331_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_331_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_fst_322_; 
v_fst_322_ = lean_ctor_get(v_a_318_, 0);
lean_inc(v_fst_322_);
lean_dec(v_a_318_);
if (lean_obj_tag(v_fst_322_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_box(0);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_323_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_object* v_val_327_; lean_object* v___x_329_; 
v_val_327_ = lean_ctor_get(v_fst_322_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v_fst_322_, 1);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_val_327_);
v___x_329_ = v___x_320_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_val_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_317_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_317_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
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
v___jp_282_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* v_e_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(v_e_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec(v_a_341_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_e_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_inst_358_, lean_object* v_a_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_353_, v_a_354_, v_e_355_, v_a_356_, v_a_357_, v_a_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args){
lean_object* v_a_372_ = _args[0];
lean_object* v_a_373_ = _args[1];
lean_object* v_e_374_ = _args[2];
lean_object* v_a_375_ = _args[3];
lean_object* v_a_376_ = _args[4];
lean_object* v_inst_377_ = _args[5];
lean_object* v_a_378_ = _args[6];
lean_object* v___y_379_ = _args[7];
lean_object* v___y_380_ = _args[8];
lean_object* v___y_381_ = _args[9];
lean_object* v___y_382_ = _args[10];
lean_object* v___y_383_ = _args[11];
lean_object* v___y_384_ = _args[12];
lean_object* v___y_385_ = _args[13];
lean_object* v___y_386_ = _args[14];
lean_object* v___y_387_ = _args[15];
lean_object* v___y_388_ = _args[16];
lean_object* v___y_389_ = _args[17];
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_372_, v_a_373_, v_e_374_, v_a_375_, v_a_376_, v_inst_377_, v_a_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v_a_373_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_393_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
v___x_394_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_392_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15____boxed(lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
return v_res_396_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
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
