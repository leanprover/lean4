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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
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
lean_object* v_snd_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_252_; 
v_snd_61_ = lean_ctor_get(v_a_49_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_49_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_a_49_, 0);
lean_dec(v_unused_253_);
v___x_63_ = v_a_49_;
v_isShared_64_ = v_isSharedCheck_252_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_snd_61_);
lean_dec(v_a_49_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_252_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_st_ref_get(v___y_50_);
lean_inc(v_snd_61_);
v___x_67_ = l_Lean_Meta_Grind_Goal_getENode(v___x_66_, v_snd_61_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___x_66_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_243_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_243_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_243_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_243_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_self_72_; lean_object* v_next_73_; lean_object* v___y_90_; lean_object* v___x_99_; 
v_self_72_ = lean_ctor_get(v_a_68_, 0);
lean_inc_ref_n(v_self_72_, 2);
v_next_73_ = lean_ctor_get(v_a_68_, 1);
lean_inc_ref(v_next_73_);
lean_dec(v_a_68_);
v___x_99_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_72_, v___y_57_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = l_Lean_Expr_cleanupAnnotations(v_a_100_);
lean_dec(v_a_100_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_103_ = lean_box(0);
v___x_104_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_103_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_104_;
goto v___jp_89_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_106_ = l_Lean_Expr_isApp(v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_107_ = lean_box(0);
v___x_108_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_107_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_108_;
goto v___jp_89_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_105_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_111_ = lean_box(0);
v___x_112_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_111_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_112_;
goto v___jp_89_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_114_ = l_Lean_Expr_isApp(v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_115_ = lean_box(0);
v___x_116_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_115_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_116_;
goto v___jp_89_;
}
else
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_113_);
v___x_118_ = l_Lean_Expr_isApp(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec_ref(v___x_117_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_119_ = lean_box(0);
v___x_120_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_119_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_120_;
goto v___jp_89_;
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_117_);
v___x_122_ = l_Lean_Expr_isApp(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v___x_117_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_123_ = lean_box(0);
v___x_124_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_123_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_124_;
goto v___jp_89_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_121_);
v___x_126_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
lean_dec_ref(v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v___x_117_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
v___x_128_ = lean_box(0);
v___x_129_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_128_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_129_;
goto v___jp_89_;
}
else
{
lean_object* v_arg_130_; size_t v___x_131_; size_t v___x_132_; uint8_t v___x_133_; 
v_arg_130_ = lean_ctor_get(v___x_121_, 1);
lean_inc_ref(v_arg_130_);
lean_dec_ref(v___x_121_);
v___x_131_ = lean_ptr_addr(v_a_45_);
v___x_132_ = lean_ptr_addr(v_arg_130_);
lean_dec_ref(v_arg_130_);
v___x_133_ = lean_usize_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec_ref(v___x_117_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
goto v___jp_74_;
}
else
{
lean_object* v_arg_134_; size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v_arg_134_ = lean_ctor_get(v___x_117_, 1);
lean_inc_ref(v_arg_134_);
lean_dec_ref(v___x_117_);
v___x_135_ = lean_ptr_addr(v_a_45_);
v___x_136_ = lean_ptr_addr(v_arg_134_);
lean_dec_ref(v_arg_134_);
v___x_137_ = lean_usize_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
goto v___jp_74_;
}
else
{
lean_object* v_arg_138_; size_t v___x_139_; size_t v___x_140_; uint8_t v___x_141_; 
v_arg_138_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_arg_138_);
lean_dec_ref(v___x_113_);
v___x_139_ = lean_ptr_addr(v_a_45_);
v___x_140_ = lean_ptr_addr(v_arg_138_);
lean_dec_ref(v_arg_138_);
v___x_141_ = lean_usize_dec_eq(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_self_72_);
goto v___jp_74_;
}
else
{
lean_object* v_arg_142_; lean_object* v_arg_143_; lean_object* v_arg_144_; lean_object* v___x_145_; 
v_arg_142_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_142_);
lean_dec_ref(v___x_101_);
v_arg_143_ = lean_ctor_get(v___x_105_, 1);
lean_inc_ref(v_arg_143_);
lean_dec_ref(v___x_105_);
v_arg_144_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_144_);
lean_dec_ref(v___x_109_);
v___x_145_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_144_, v___y_57_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; uint8_t v___x_147_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref_known(v___x_145_, 1);
v___x_147_ = lean_unbox(v_a_146_);
lean_dec(v_a_146_);
if (v___x_147_ == 0)
{
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_self_72_);
goto v___jp_74_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Expr_appFn_x21(v_e_46_);
v___x_149_ = l_Lean_Expr_appFn_x21(v___x_148_);
lean_dec_ref(v___x_148_);
lean_inc_ref(v_arg_143_);
lean_inc_ref_n(v_a_47_, 2);
lean_inc_ref(v___x_149_);
v___x_150_ = l_Lean_mkAppB(v___x_149_, v_a_47_, v_arg_143_);
lean_inc_ref(v_arg_142_);
v___x_151_ = l_Lean_mkAppB(v___x_149_, v_a_47_, v_arg_142_);
v___x_152_ = l_Lean_Meta_mkMul(v___x_150_, v___x_151_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
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
v___x_154_ = lean_grind_preprocess(v_a_153_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_46_, v___y_50_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v_expr_158_; lean_object* v___x_159_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v_expr_158_ = lean_ctor_get(v_a_155_, 0);
lean_inc_ref_n(v_expr_158_, 2);
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
v___x_159_ = lean_grind_internalize(v_expr_158_, v_a_157_, v___x_65_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref_known(v___x_159_, 1);
v___x_160_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8));
lean_inc_ref(v_a_48_);
v___x_161_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_160_, v_a_48_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_161_, 1);
if (lean_obj_tag(v_a_162_) == 1)
{
lean_object* v_val_163_; lean_object* v___x_164_; 
v_val_163_ = lean_ctor_get(v_a_162_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v_a_162_, 1);
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
v___x_164_ = lean_grind_mk_eq_proof(v_a_44_, v_self_72_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = l_Lean_Meta_Simp_Result_getProof(v_a_155_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
lean_inc_ref(v_a_44_);
lean_inc_ref(v_expr_158_);
lean_inc_ref(v_a_47_);
v___x_168_ = l_Lean_mkApp7(v_val_163_, v_a_47_, v_expr_158_, v_a_44_, v_arg_143_, v_arg_142_, v_a_165_, v_a_167_);
v___x_169_ = 0;
lean_inc_ref(v_e_46_);
v___x_170_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_46_, v_expr_158_, v___x_168_, v___x_169_, v___y_50_, v___y_52_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
v___y_90_ = v___x_170_;
goto v___jp_89_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_a_165_);
lean_dec(v_val_163_);
lean_dec_ref(v_expr_158_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_171_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_166_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_166_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_val_163_);
lean_dec_ref(v_expr_158_);
lean_dec(v_a_155_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_179_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_164_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_164_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_dec(v_a_162_);
lean_dec_ref(v_expr_158_);
lean_dec(v_a_155_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_self_72_);
goto v___jp_74_;
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec_ref(v_expr_158_);
lean_dec(v_a_155_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_187_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_161_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_161_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec_ref(v_expr_158_);
lean_dec(v_a_155_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_195_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_159_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_159_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec(v_a_155_);
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_203_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_156_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_156_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_211_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_154_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_154_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_219_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_152_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_152_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_227_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_145_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_145_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
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
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_next_73_);
lean_dec_ref(v_self_72_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_235_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_99_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_99_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
v___jp_74_:
{
size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_ptr_addr(v_next_73_);
v___x_76_ = lean_ptr_addr(v_a_44_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_79_; 
lean_del_object(v___x_70_);
lean_dec(v_snd_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_next_73_);
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_79_ = v___x_63_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_next_73_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
v_a_49_ = v___x_79_;
goto _start;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec_ref(v_next_73_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v___x_82_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0));
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_82_);
v___x_84_ = v___x_63_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_snd_61_);
v___x_84_ = v_reuseFailAlloc_88_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_86_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_84_);
v___x_86_ = v___x_70_;
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
lean_dec_ref_known(v___y_90_, 1);
goto v___jp_74_;
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec_ref(v_next_73_);
lean_del_object(v___x_70_);
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
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
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_del_object(v___x_63_);
lean_dec(v_snd_61_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_a_44_);
v_a_244_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_67_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_67_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_a_254_ = _args[0];
lean_object* v_a_255_ = _args[1];
lean_object* v_e_256_ = _args[2];
lean_object* v_a_257_ = _args[3];
lean_object* v_a_258_ = _args[4];
lean_object* v_a_259_ = _args[5];
lean_object* v___y_260_ = _args[6];
lean_object* v___y_261_ = _args[7];
lean_object* v___y_262_ = _args[8];
lean_object* v___y_263_ = _args[9];
lean_object* v___y_264_ = _args[10];
lean_object* v___y_265_ = _args[11];
lean_object* v___y_266_ = _args[12];
lean_object* v___y_267_ = _args[13];
lean_object* v___y_268_ = _args[14];
lean_object* v___y_269_ = _args[15];
lean_object* v___y_270_ = _args[16];
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_254_, v_a_255_, v_e_256_, v_a_257_, v_a_258_, v_a_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v_a_255_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = l_Lean_Expr_cleanupAnnotations(v_e_280_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_300_ = l_Lean_Expr_isApp(v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v___x_299_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_299_);
lean_dec_ref(v___x_299_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_304_ = l_Lean_Expr_isApp(v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_306_ = l_Lean_Expr_isApp(v___x_305_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_305_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_308_);
lean_dec_ref(v___x_307_);
if (v___x_309_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_arg_310_ = lean_ctor_get(v___x_303_, 1);
lean_inc_ref(v_arg_310_);
lean_dec_ref(v___x_303_);
v___x_311_ = l_Lean_Expr_cleanupAnnotations(v_arg_310_);
v___x_312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_311_, v___x_312_);
lean_dec_ref(v___x_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v_arg_310_);
lean_dec_ref(v___x_305_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v_arg_316_; lean_object* v_arg_317_; size_t v___x_318_; size_t v___x_319_; uint8_t v___x_320_; 
v_arg_316_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_316_);
lean_dec_ref(v___x_301_);
v_arg_317_ = lean_ctor_get(v___x_305_, 1);
lean_inc_ref(v_arg_317_);
lean_dec_ref(v___x_305_);
v___x_318_ = lean_ptr_addr(v_arg_317_);
v___x_319_ = lean_ptr_addr(v_arg_316_);
lean_dec_ref(v_arg_316_);
v___x_320_ = lean_usize_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_arg_317_);
lean_dec_ref(v_arg_310_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_e_280_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v_arg_323_; lean_object* v_arg_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_arg_323_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref_n(v_arg_323_, 2);
lean_dec_ref(v___x_295_);
v_arg_324_ = lean_ctor_get(v___x_297_, 1);
lean_inc_ref(v_arg_324_);
lean_dec_ref(v___x_297_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_arg_323_);
v___x_327_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_arg_323_, v_arg_310_, v_e_280_, v_arg_324_, v_arg_317_, v___x_326_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec_ref(v_arg_310_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_341_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_341_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_341_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_341_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_fst_332_; 
v_fst_332_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_fst_332_);
lean_dec(v_a_328_);
if (lean_obj_tag(v_fst_332_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v_val_337_; lean_object* v___x_339_; 
v_val_337_ = lean_ctor_get(v_fst_332_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v_fst_332_, 1);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v_val_337_);
v___x_339_ = v___x_330_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_val_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
v_a_342_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_327_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_327_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
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
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* v_e_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(v_e_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_inst_368_, lean_object* v_a_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_363_, v_a_364_, v_e_365_, v_a_366_, v_a_367_, v_a_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args){
lean_object* v_a_382_ = _args[0];
lean_object* v_a_383_ = _args[1];
lean_object* v_e_384_ = _args[2];
lean_object* v_a_385_ = _args[3];
lean_object* v_a_386_ = _args[4];
lean_object* v_inst_387_ = _args[5];
lean_object* v_a_388_ = _args[6];
lean_object* v___y_389_ = _args[7];
lean_object* v___y_390_ = _args[8];
lean_object* v___y_391_ = _args[9];
lean_object* v___y_392_ = _args[10];
lean_object* v___y_393_ = _args[11];
lean_object* v___y_394_ = _args[12];
lean_object* v___y_395_ = _args[13];
lean_object* v___y_396_ = _args[14];
lean_object* v___y_397_ = _args[15];
lean_object* v___y_398_ = _args[16];
lean_object* v___y_399_ = _args[17];
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_382_, v_a_383_, v_e_384_, v_a_385_, v_a_386_, v_inst_387_, v_a_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v_a_383_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_403_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
v___x_404_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15____boxed(lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
return v_res_406_;
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
