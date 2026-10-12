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
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v_res_15_;
v_res_15_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0___boxed(lean_object* v_x_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v_x_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
return v_res_28_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_243_; 
v_snd_62_ = lean_ctor_get(v_a_50_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_a_50_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_a_50_, 0);
lean_dec(v_unused_244_);
v___x_64_ = v_a_50_;
v_isShared_65_ = v_isSharedCheck_243_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_dec(v_a_50_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_243_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_box(0);
v___x_67_ = lean_st_ref_get(v___y_51_);
lean_inc(v_snd_62_);
v___x_68_ = l_Lean_Meta_Grind_Goal_getENode(v___x_67_, v_snd_62_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___x_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_234_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_234_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_234_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_234_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_self_73_; lean_object* v_next_74_; lean_object* v___y_91_; lean_object* v___x_100_; 
v_self_73_ = lean_ctor_get(v_a_69_, 0);
lean_inc_ref_n(v_self_73_, 2);
v_next_74_ = lean_ctor_get(v_a_69_, 1);
lean_inc_ref(v_next_74_);
lean_dec(v_a_69_);
v___x_100_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_73_, v___y_58_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_102_ = l_Lean_Expr_cleanupAnnotations(v_a_101_);
v___x_103_ = l_Lean_Expr_isApp(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec_ref(v___x_102_);
lean_dec_ref(v_self_73_);
v___x_104_ = lean_box(0);
v___x_105_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_104_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_105_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_106_ = lean_ctor_get(v___x_102_, 1);
lean_inc_ref(v_arg_106_);
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_102_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_109_ = lean_box(0);
v___x_110_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_109_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_110_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_arg_111_ = lean_ctor_get(v___x_107_, 1);
lean_inc_ref(v_arg_111_);
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_114_ = lean_box(0);
v___x_115_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_114_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_115_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_arg_116_ = lean_ctor_get(v___x_112_, 1);
lean_inc_ref(v_arg_116_);
v___x_117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_118_ = l_Lean_Expr_isApp(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec_ref(v___x_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_119_ = lean_box(0);
v___x_120_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_119_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_120_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_arg_121_ = lean_ctor_get(v___x_117_, 1);
lean_inc_ref(v_arg_121_);
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_117_);
v___x_123_ = l_Lean_Expr_isApp(v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec_ref(v___x_122_);
lean_dec_ref(v_arg_121_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_124_ = lean_box(0);
v___x_125_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_124_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_125_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_arg_126_ = lean_ctor_get(v___x_122_, 1);
lean_inc_ref(v_arg_126_);
v___x_127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_122_);
v___x_128_ = l_Lean_Expr_isApp(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v___x_127_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_121_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_129_ = lean_box(0);
v___x_130_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_129_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_130_;
goto v___jp_90_;
}
else
{
lean_object* v_arg_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_arg_131_ = lean_ctor_get(v___x_127_, 1);
lean_inc_ref(v_arg_131_);
v___x_132_ = l_Lean_Expr_appFnCleanup___redArg(v___x_127_);
v___x_133_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3));
v___x_134_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_133_);
lean_dec_ref(v___x_132_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec_ref(v_arg_131_);
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_121_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___x_135_ = lean_box(0);
v___x_136_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_135_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_136_;
goto v___jp_90_;
}
else
{
size_t v___x_137_; size_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_ptr_addr(v_a_46_);
v___x_138_ = lean_ptr_addr(v_arg_131_);
lean_dec_ref(v_arg_131_);
v___x_139_ = lean_usize_dec_eq(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_dec_ref(v_arg_126_);
lean_dec_ref(v_arg_121_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
goto v___jp_75_;
}
else
{
size_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_ptr_addr(v_arg_126_);
lean_dec_ref(v_arg_126_);
v___x_141_ = lean_usize_dec_eq(v___x_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec_ref(v_arg_121_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
goto v___jp_75_;
}
else
{
size_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_ptr_addr(v_arg_121_);
lean_dec_ref(v_arg_121_);
v___x_143_ = lean_usize_dec_eq(v___x_137_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
goto v___jp_75_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_116_, v___y_58_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; uint8_t v___x_146_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
lean_dec_ref_known(v___x_144_, 1);
v___x_146_ = lean_unbox(v_a_145_);
lean_dec(v_a_145_);
if (v___x_146_ == 0)
{
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
goto v___jp_75_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = l_Lean_Expr_appFn_x21(v_e_47_);
v___x_148_ = l_Lean_Expr_appFn_x21(v___x_147_);
lean_dec_ref(v___x_147_);
lean_inc_ref(v_arg_111_);
lean_inc_ref_n(v_a_48_, 2);
lean_inc_ref(v___x_148_);
v___x_149_ = l_Lean_mkAppB(v___x_148_, v_a_48_, v_arg_111_);
lean_inc_ref(v_arg_106_);
v___x_150_ = l_Lean_mkAppB(v___x_148_, v_a_48_, v_arg_106_);
v___x_151_ = l_Lean_Meta_mkMul(v___x_149_, v___x_150_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc(v___y_51_);
v___x_153_ = lean_grind_preprocess(v_a_152_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_47_, v___y_51_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v_expr_157_; lean_object* v___x_158_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v_expr_157_ = lean_ctor_get(v_a_154_, 0);
lean_inc_ref_n(v_expr_157_, 2);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc(v___y_51_);
v___x_158_ = lean_grind_internalize(v_expr_157_, v_a_156_, v___x_66_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec_ref_known(v___x_158_, 1);
v___x_159_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8));
lean_inc_ref(v_a_49_);
v___x_160_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(v___x_159_, v_a_49_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
if (lean_obj_tag(v_a_161_) == 1)
{
lean_object* v_val_162_; lean_object* v___x_163_; 
v_val_162_ = lean_ctor_get(v_a_161_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v_a_161_, 1);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc(v___y_51_);
lean_inc_ref(v_a_45_);
v___x_163_ = lean_grind_mk_eq_proof(v_a_45_, v_self_73_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = l_Lean_Meta_Simp_Result_getProof(v_a_154_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
lean_inc_ref(v_a_45_);
lean_inc_ref(v_expr_157_);
lean_inc_ref(v_a_48_);
v___x_167_ = l_Lean_mkApp7(v_val_162_, v_a_48_, v_expr_157_, v_a_45_, v_arg_111_, v_arg_106_, v_a_164_, v_a_166_);
v___x_168_ = 0;
lean_inc_ref(v_e_47_);
v___x_169_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_47_, v_expr_157_, v___x_167_, v___x_168_, v___y_51_, v___y_53_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v___y_91_ = v___x_169_;
goto v___jp_90_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_a_164_);
lean_dec(v_val_162_);
lean_dec_ref(v_expr_157_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_170_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_165_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v_val_162_);
lean_dec_ref(v_expr_157_);
lean_dec(v_a_154_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_178_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_163_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_163_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_dec(v_a_161_);
lean_dec_ref(v_expr_157_);
lean_dec(v_a_154_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
goto v___jp_75_;
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_expr_157_);
lean_dec(v_a_154_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_186_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_160_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_160_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_dec_ref(v_expr_157_);
lean_dec(v_a_154_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_self_73_);
v___y_91_ = v___x_158_;
goto v___jp_90_;
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_154_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_194_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_155_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_155_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_202_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_153_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_153_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_210_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_151_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_151_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_218_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_144_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_144_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
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
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_next_74_);
lean_dec_ref(v_self_73_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_226_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_100_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_100_);
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
v___jp_75_:
{
size_t v___x_76_; size_t v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_ptr_addr(v_next_74_);
v___x_77_ = lean_ptr_addr(v_a_45_);
v___x_78_ = lean_usize_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_71_);
lean_dec(v_snd_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v_next_74_);
lean_ctor_set(v___x_64_, 0, v___x_66_);
v___x_80_ = v___x_64_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_next_74_);
v___x_80_ = v_reuseFailAlloc_82_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v_a_50_ = v___x_80_;
goto _start;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_85_; 
lean_dec_ref(v_next_74_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v___x_83_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0));
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_83_);
v___x_85_ = v___x_64_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_snd_62_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_85_);
v___x_87_ = v___x_71_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
v___jp_90_:
{
if (lean_obj_tag(v___y_91_) == 0)
{
lean_dec_ref_known(v___y_91_, 1);
goto v___jp_75_;
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_next_74_);
lean_del_object(v___x_71_);
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_92_ = lean_ctor_get(v___y_91_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___y_91_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___y_91_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___y_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_del_object(v___x_64_);
lean_dec(v_snd_62_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_e_47_);
lean_dec_ref(v_a_45_);
v_a_235_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_68_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_68_);
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
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_45_ = stack[0].m_obj;
lean_object* v_a_46_ = stack[1].m_obj;
lean_object* v_e_47_ = stack[2].m_obj;
lean_object* v_a_48_ = stack[3].m_obj;
lean_object* v_a_49_ = stack[4].m_obj;
lean_object* v_a_50_ = stack[5].m_obj;
lean_object* v___y_51_ = stack[6].m_obj;
lean_object* v___y_52_ = stack[7].m_obj;
lean_object* v___y_53_ = stack[8].m_obj;
lean_object* v___y_54_ = stack[9].m_obj;
lean_object* v___y_55_ = stack[10].m_obj;
lean_object* v___y_56_ = stack[11].m_obj;
lean_object* v___y_57_ = stack[12].m_obj;
lean_object* v___y_58_ = stack[13].m_obj;
lean_object* v___y_59_ = stack[14].m_obj;
lean_object* v___y_60_ = stack[15].m_obj;
lean_object* v_res_245_;
v_res_245_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_45_, v_a_46_, v_e_47_, v_a_48_, v_a_49_, v_a_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_a_246_ = _args[0];
lean_object* v_a_247_ = _args[1];
lean_object* v_e_248_ = _args[2];
lean_object* v_a_249_ = _args[3];
lean_object* v_a_250_ = _args[4];
lean_object* v_a_251_ = _args[5];
lean_object* v___y_252_ = _args[6];
lean_object* v___y_253_ = _args[7];
lean_object* v___y_254_ = _args[8];
lean_object* v___y_255_ = _args[9];
lean_object* v___y_256_ = _args[10];
lean_object* v___y_257_ = _args[11];
lean_object* v___y_258_ = _args[12];
lean_object* v___y_259_ = _args[13];
lean_object* v___y_260_ = _args[14];
lean_object* v___y_261_ = _args[15];
lean_object* v___y_262_ = _args[16];
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_246_, v_a_247_, v_e_248_, v_a_249_, v_a_250_, v_a_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_a_247_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
lean_inc_ref(v_e_272_);
v___x_287_ = l_Lean_Expr_cleanupAnnotations(v_e_272_);
v___x_288_ = l_Lean_Expr_isApp(v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v_arg_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_arg_289_ = lean_ctor_get(v___x_287_, 1);
lean_inc_ref(v_arg_289_);
v___x_290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_287_);
v___x_291_ = l_Lean_Expr_isApp(v___x_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v___x_290_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v_arg_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_arg_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc_ref(v_arg_292_);
v___x_293_ = l_Lean_Expr_appFnCleanup___redArg(v___x_290_);
v___x_294_ = l_Lean_Expr_isApp(v___x_293_);
if (v___x_294_ == 0)
{
lean_dec_ref(v___x_293_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_293_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v_arg_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_arg_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref(v_arg_297_);
v___x_298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_299_ = l_Lean_Expr_isApp(v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v___x_298_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v_arg_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_arg_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc_ref(v_arg_300_);
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_298_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v_arg_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_arg_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_303_);
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_305_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_305_);
lean_dec_ref(v___x_304_);
if (v___x_306_ == 0)
{
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
goto v___jp_284_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
lean_inc_ref(v_arg_300_);
v___x_307_ = l_Lean_Expr_cleanupAnnotations(v_arg_300_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_308_);
lean_dec_ref(v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_arg_297_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_ptr_addr(v_arg_303_);
v___x_313_ = lean_ptr_addr(v_arg_297_);
lean_dec_ref(v_arg_297_);
v___x_314_ = lean_usize_dec_eq(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_e_272_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
lean_inc_ref(v_arg_289_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_arg_289_);
v___x_319_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_arg_289_, v_arg_300_, v_e_272_, v_arg_292_, v_arg_303_, v___x_318_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec_ref(v_arg_300_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_333_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_333_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_333_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_333_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_fst_324_; 
v_fst_324_ = lean_ctor_get(v_a_320_, 0);
lean_inc(v_fst_324_);
lean_dec(v_a_320_);
if (lean_obj_tag(v_fst_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v_val_329_; lean_object* v___x_331_; 
v_val_329_ = lean_ctor_get(v_fst_324_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v_fst_324_, 1);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v_val_329_);
v___x_331_ = v___x_322_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_val_329_);
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
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_319_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_319_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
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
}
}
}
}
}
}
}
}
v___jp_284_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_propagatePower_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_272_ = stack[0].m_obj;
lean_object* v_a_273_ = stack[1].m_obj;
lean_object* v_a_274_ = stack[2].m_obj;
lean_object* v_a_275_ = stack[3].m_obj;
lean_object* v_a_276_ = stack[4].m_obj;
lean_object* v_a_277_ = stack[5].m_obj;
lean_object* v_a_278_ = stack[6].m_obj;
lean_object* v_a_279_ = stack[7].m_obj;
lean_object* v_a_280_ = stack[8].m_obj;
lean_object* v_a_281_ = stack[9].m_obj;
lean_object* v_a_282_ = stack[10].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(v_e_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec(v_a_344_);
return v_res_355_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_inst_361_, lean_object* v_a_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_356_, v_a_357_, v_e_358_, v_a_359_, v_a_360_, v_a_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_374_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_356_ = stack[0].m_obj;
lean_object* v_a_357_ = stack[1].m_obj;
lean_object* v_e_358_ = stack[2].m_obj;
lean_object* v_a_359_ = stack[3].m_obj;
lean_object* v_a_360_ = stack[4].m_obj;
lean_object* v_a_362_ = stack[6].m_obj;
lean_object* v___y_363_ = stack[7].m_obj;
lean_object* v___y_364_ = stack[8].m_obj;
lean_object* v___y_365_ = stack[9].m_obj;
lean_object* v___y_366_ = stack[10].m_obj;
lean_object* v___y_367_ = stack[11].m_obj;
lean_object* v___y_368_ = stack[12].m_obj;
lean_object* v___y_369_ = stack[13].m_obj;
lean_object* v___y_370_ = stack[14].m_obj;
lean_object* v___y_371_ = stack[15].m_obj;
lean_object* v___y_372_ = stack[16].m_obj;
lean_object* v_res_375_;
v_res_375_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_356_, v_a_357_, v_e_358_, v_a_359_, v_a_360_, lean_box(0), v_a_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args){
lean_object* v_a_376_ = _args[0];
lean_object* v_a_377_ = _args[1];
lean_object* v_e_378_ = _args[2];
lean_object* v_a_379_ = _args[3];
lean_object* v_a_380_ = _args[4];
lean_object* v_inst_381_ = _args[5];
lean_object* v_a_382_ = _args[6];
lean_object* v___y_383_ = _args[7];
lean_object* v___y_384_ = _args[8];
lean_object* v___y_385_ = _args[9];
lean_object* v___y_386_ = _args[10];
lean_object* v___y_387_ = _args[11];
lean_object* v___y_388_ = _args[12];
lean_object* v___y_389_ = _args[13];
lean_object* v___y_390_ = _args[14];
lean_object* v___y_391_ = _args[15];
lean_object* v___y_392_ = _args[16];
lean_object* v___y_393_ = _args[17];
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_376_, v_a_377_, v_e_378_, v_a_379_, v_a_380_, v_inst_381_, v_a_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v_a_377_);
return v_res_394_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
v___x_397_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
v___x_398_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_396_, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_399_;
v_res_399_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15____boxed(lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_15_();
return v_res_401_;
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
