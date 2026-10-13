// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallAnd
// Imports: public import Lean.Meta.Basic import Init.Grind.Norm import Lean.Meta.InferType import Lean.Meta.AppBuilder
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
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTransCoreProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "forall_and"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 10, 210, 75, 235, 208, 8, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(213, 145, 235, 56, 9, 236, 160, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implies_congr_right"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 214, 41, 106, 32, 244, 82, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(lean_object* v_a_1_){
_start:
{
if (lean_obj_tag(v_a_1_) == 7)
{
lean_object* v_body_2_; lean_object* v___x_3_; uint8_t v___x_4_; 
v_body_2_ = lean_ctor_get(v_a_1_, 2);
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_expr_has_loose_bvar(v_body_2_, v___x_3_);
if (v___x_4_ == 0)
{
v_a_1_ = v_body_2_;
goto _start;
}
else
{
return v___x_4_;
}
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 0;
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder___boxed(lean_object* v_a_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_a_7_);
lean_dec_ref(v_a_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(lean_object* v_e_13_){
_start:
{
uint8_t v___y_15_; uint8_t v___x_17_; 
v___x_17_ = l_Lean_Expr_isForall(v_e_13_);
if (v___x_17_ == 0)
{
v___y_15_ = v___x_17_;
goto v___jp_14_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_18_ = l_Lean_Expr_getForallBody(v_e_13_);
v___x_19_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_20_ = lean_unsigned_to_nat(2u);
v___x_21_ = l_Lean_Expr_isAppOfArity(v___x_18_, v___x_19_, v___x_20_);
lean_dec_ref(v___x_18_);
v___y_15_ = v___x_21_;
goto v___jp_14_;
}
v___jp_14_:
{
if (v___y_15_ == 0)
{
return v___y_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_e_13_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___boxed(lean_object* v_e_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_22_);
lean_dec_ref(v_e_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(lean_object* v_k_25_, lean_object* v_b_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; 
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
v___x_32_ = lean_apply_6(v_k_25_, v_b_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, lean_box(0));
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_33_, lean_object* v_b_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(v_k_33_, v_b_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(lean_object* v_name_41_, uint8_t v_bi_42_, lean_object* v_type_43_, lean_object* v_k_44_, uint8_t v_kind_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_52_; 
v___f_51_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_51_, 0, v_k_44_);
v___x_52_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_41_, v_bi_42_, v_type_43_, v___f_51_, v_kind_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_52_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_52_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___boxed(lean_object* v_name_69_, lean_object* v_bi_70_, lean_object* v_type_71_, lean_object* v_k_72_, lean_object* v_kind_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_bi_boxed_79_; uint8_t v_kind_boxed_80_; lean_object* v_res_81_; 
v_bi_boxed_79_ = lean_unbox(v_bi_70_);
v_kind_boxed_80_ = lean_unbox(v_kind_73_);
v_res_81_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_69_, v_bi_boxed_79_, v_type_71_, v_k_72_, v_kind_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(lean_object* v_00_u03b1_82_, lean_object* v_name_83_, uint8_t v_bi_84_, lean_object* v_type_85_, lean_object* v_k_86_, uint8_t v_kind_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_83_, v_bi_84_, v_type_85_, v_k_86_, v_kind_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_94_, lean_object* v_name_95_, lean_object* v_bi_96_, lean_object* v_type_97_, lean_object* v_k_98_, lean_object* v_kind_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
uint8_t v_bi_boxed_105_; uint8_t v_kind_boxed_106_; lean_object* v_res_107_; 
v_bi_boxed_105_ = lean_unbox(v_bi_96_);
v_kind_boxed_106_ = lean_unbox(v_kind_99_);
v_res_107_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(v_00_u03b1_94_, v_name_95_, v_bi_boxed_105_, v_type_97_, v_k_98_, v_kind_boxed_106_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = l_Lean_Level_ofNat(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed(lean_object* v_body_126_, lean_object* v___x_127_, lean_object* v_a_128_, lean_object* v_binderType_129_, lean_object* v_t_130_, lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
uint8_t v___x_4230__boxed_137_; lean_object* v_res_138_; 
v___x_4230__boxed_137_ = lean_unbox(v___x_127_);
v_res_138_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(v_body_126_, v___x_4230__boxed_137_, v_a_128_, v_binderType_129_, v_t_130_, v_x_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec_ref(v_body_126_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(lean_object* v_t_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___x_267_; 
lean_inc_ref(v_t_143_);
v___x_267_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_143_, v_a_145_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_288_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_288_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_288_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_288_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = l_Lean_Expr_cleanupAnnotations(v_a_268_);
v___x_273_ = l_Lean_Expr_isApp(v___x_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v___x_272_);
lean_del_object(v___x_270_);
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
goto v___jp_149_;
}
else
{
lean_object* v_arg_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_arg_274_ = lean_ctor_get(v___x_272_, 1);
lean_inc_ref(v_arg_274_);
v___x_275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_272_);
v___x_276_ = l_Lean_Expr_isApp(v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v___x_275_);
lean_dec_ref(v_arg_274_);
lean_del_object(v___x_270_);
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
goto v___jp_149_;
}
else
{
lean_object* v_arg_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_arg_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc_ref(v_arg_277_);
v___x_278_ = l_Lean_Expr_appFnCleanup___redArg(v___x_275_);
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_280_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_279_);
lean_dec_ref(v___x_278_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_arg_277_);
lean_dec_ref(v_arg_274_);
lean_del_object(v___x_270_);
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
goto v___jp_149_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec_ref(v_t_143_);
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4));
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_arg_274_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_arg_277_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_284_);
v___x_286_ = v___x_270_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_t_143_);
v_a_289_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_267_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_267_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
v___jp_149_:
{
if (lean_obj_tag(v_t_143_) == 7)
{
lean_object* v_binderName_154_; lean_object* v_binderType_155_; lean_object* v_body_156_; uint8_t v_binderInfo_157_; lean_object* v___x_158_; 
v_binderName_154_ = lean_ctor_get(v_t_143_, 0);
v_binderType_155_ = lean_ctor_get(v_t_143_, 1);
v_body_156_ = lean_ctor_get(v_t_143_, 2);
v_binderInfo_157_ = lean_ctor_get_uint8(v_t_143_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_155_);
v___x_158_ = l_Lean_Meta_getLevel(v_binderType_155_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_Lean_Expr_hasLooseBVars(v_body_156_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_inc_ref(v_body_156_);
v___x_161_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_body_156_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_252_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_252_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_252_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_252_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
if (lean_obj_tag(v_a_162_) == 1)
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_247_; 
v_val_166_ = lean_ctor_get(v_a_162_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_247_ == 0)
{
v___x_168_ = v_a_162_;
v_isShared_169_ = v_isSharedCheck_247_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v_a_162_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_247_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_snd_170_; lean_object* v_snd_171_; lean_object* v_fst_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_245_; 
v_snd_170_ = lean_ctor_get(v_val_166_, 1);
lean_inc(v_snd_170_);
v_snd_171_ = lean_ctor_get(v_snd_170_, 1);
lean_inc(v_snd_171_);
v_fst_172_ = lean_ctor_get(v_val_166_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_val_166_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_val_166_, 1);
lean_dec(v_unused_246_);
v___x_174_ = v_val_166_;
v_isShared_175_ = v_isSharedCheck_245_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_fst_172_);
lean_dec(v_val_166_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_245_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_fst_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_243_; 
v_fst_176_ = lean_ctor_get(v_snd_170_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_snd_170_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_snd_170_, 1);
lean_dec(v_unused_244_);
v___x_178_ = v_snd_170_;
v_isShared_179_ = v_isSharedCheck_243_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_fst_176_);
lean_dec(v_snd_170_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_243_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_242_; 
v_fst_180_ = lean_ctor_get(v_snd_171_, 0);
v_snd_181_ = lean_ctor_get(v_snd_171_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_snd_171_);
if (v_isSharedCheck_242_ == 0)
{
v___x_183_ = v_snd_171_;
v_isShared_184_ = v_isSharedCheck_242_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v_snd_171_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_242_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_inc_n(v_fst_172_, 2);
lean_inc_ref_n(v_binderType_155_, 5);
lean_inc_n(v_binderName_154_, 4);
v___x_185_ = l_Lean_mkForall(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v_fst_172_);
lean_inc_n(v_fst_176_, 2);
v___x_186_ = l_Lean_mkForall(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v_fst_176_);
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_188_ = lean_box(0);
lean_inc(v_a_159_);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v_a_159_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Lean_mkConst(v___x_187_, v___x_189_);
v___x_191_ = l_Lean_mkLambda(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v_fst_172_);
v___x_192_ = l_Lean_mkLambda(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v_fst_176_);
v___x_193_ = l_Lean_mkApp3(v___x_190_, v_binderType_155_, v___x_191_, v___x_192_);
if (lean_obj_tag(v_fst_180_) == 1)
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_225_; 
v_val_194_ = lean_ctor_get(v_fst_180_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_fst_180_);
if (v_isSharedCheck_225_ == 0)
{
v___x_196_ = v_fst_180_;
v_isShared_197_ = v_isSharedCheck_225_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v_fst_180_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_225_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1));
v___x_199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v_a_159_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = l_Lean_mkConst(v___x_198_, v___x_200_);
v___x_202_ = l_Lean_mkAnd(v_fst_172_, v_fst_176_);
lean_inc_ref(v___x_202_);
lean_inc_ref(v_body_156_);
lean_inc_ref_n(v_binderType_155_, 2);
v___x_203_ = l_Lean_mkApp4(v___x_201_, v_binderType_155_, v_body_156_, v___x_202_, v_val_194_);
lean_inc(v_binderName_154_);
v___x_204_ = l_Lean_mkForall(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v___x_202_);
lean_inc_ref(v___x_186_);
lean_inc_ref(v___x_185_);
v___x_205_ = l_Lean_mkAnd(v___x_185_, v___x_186_);
v___x_206_ = l_Lean_Meta_mkEqTransCoreProp(v_t_143_, v___x_204_, v___x_205_, v___x_203_, v___x_193_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_206_);
v___x_208_ = v___x_196_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_224_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_208_);
v___x_210_ = v___x_183_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_snd_181_);
v___x_210_ = v_reuseFailAlloc_223_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_210_);
lean_ctor_set(v___x_178_, 0, v___x_186_);
v___x_212_ = v___x_178_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_222_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_212_);
lean_ctor_set(v___x_174_, 0, v___x_185_);
v___x_214_ = v___x_174_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_221_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_214_);
v___x_216_ = v___x_168_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_216_);
v___x_218_ = v___x_164_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
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
lean_object* v___x_227_; 
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
lean_dec(v_fst_172_);
lean_dec(v_a_159_);
lean_dec_ref_known(v_t_143_, 3);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_193_);
v___x_227_ = v___x_168_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_193_);
v___x_227_ = v_reuseFailAlloc_241_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_227_);
v___x_229_ = v___x_183_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_snd_181_);
v___x_229_ = v_reuseFailAlloc_240_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_229_);
lean_ctor_set(v___x_178_, 0, v___x_186_);
v___x_231_ = v___x_178_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_239_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_231_);
lean_ctor_set(v___x_174_, 0, v___x_185_);
v___x_233_ = v___x_174_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_238_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_234_);
v___x_236_ = v___x_164_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
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
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_dec(v_a_162_);
lean_dec(v_a_159_);
lean_dec_ref_known(v_t_143_, 3);
v___x_248_ = lean_box(0);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_248_);
v___x_250_ = v___x_164_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_dec(v_a_159_);
lean_dec_ref_known(v_t_143_, 3);
return v___x_161_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___f_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
lean_inc_ref(v_body_156_);
lean_inc_ref_n(v_binderType_155_, 2);
lean_inc(v_binderName_154_);
v___x_253_ = lean_box(v___x_160_);
v___f_254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed), 11, 5);
lean_closure_set(v___f_254_, 0, v_body_156_);
lean_closure_set(v___f_254_, 1, v___x_253_);
lean_closure_set(v___f_254_, 2, v_a_159_);
lean_closure_set(v___f_254_, 3, v_binderType_155_);
lean_closure_set(v___f_254_, 4, v_t_143_);
v___x_255_ = 0;
v___x_256_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_binderName_154_, v_binderInfo_157_, v_binderType_155_, v___f_254_, v___x_255_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_256_;
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref_known(v_t_143_, 3);
v_a_257_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_158_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_158_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v_t_143_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(lean_object* v_body_297_, uint8_t v___x_298_, lean_object* v_a_299_, lean_object* v_binderType_300_, lean_object* v_t_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_expr_instantiate1(v_body_297_, v_x_302_);
lean_inc_ref(v___x_308_);
v___x_309_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v___x_308_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_488_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_488_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_488_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_488_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_a_310_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_483_; 
lean_del_object(v___x_312_);
v_val_314_ = lean_ctor_get(v_a_310_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_483_ == 0)
{
v___x_316_ = v_a_310_;
v_isShared_317_ = v_isSharedCheck_483_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_val_314_);
lean_dec(v_a_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_483_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_snd_318_; lean_object* v_snd_319_; lean_object* v_fst_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_481_; 
v_snd_318_ = lean_ctor_get(v_val_314_, 1);
lean_inc(v_snd_318_);
v_snd_319_ = lean_ctor_get(v_snd_318_, 1);
lean_inc(v_snd_319_);
v_fst_320_ = lean_ctor_get(v_val_314_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_val_314_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v_val_314_, 1);
lean_dec(v_unused_482_);
v___x_322_ = v_val_314_;
v_isShared_323_ = v_isSharedCheck_481_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_fst_320_);
lean_dec(v_val_314_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_481_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_fst_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_479_; 
v_fst_324_ = lean_ctor_get(v_snd_318_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_snd_318_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_snd_318_, 1);
lean_dec(v_unused_480_);
v___x_326_ = v_snd_318_;
v_isShared_327_ = v_isSharedCheck_479_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_fst_324_);
lean_dec(v_snd_318_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_479_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_fst_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_477_; 
v_fst_328_ = lean_ctor_get(v_snd_319_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_snd_319_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_snd_319_, 1);
lean_dec(v_unused_478_);
v___x_330_ = v_snd_319_;
v_isShared_331_ = v_isSharedCheck_477_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_fst_328_);
lean_dec(v_snd_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_477_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
v___x_334_ = lean_array_push(v___x_333_, v_x_302_);
v___x_335_ = 0;
v___x_336_ = 1;
lean_inc(v_fst_320_);
v___x_337_ = l_Lean_Meta_mkForallFVars(v___x_334_, v_fst_320_, v___x_335_, v___x_298_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
lean_inc(v_fst_324_);
v___x_339_ = l_Lean_Meta_mkForallFVars(v___x_334_, v_fst_324_, v___x_335_, v___x_298_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
lean_inc(v_fst_320_);
v___x_341_ = l_Lean_Meta_mkLambdaFVars(v___x_334_, v_fst_320_, v___x_335_, v___x_298_, v___x_335_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
lean_inc(v_fst_324_);
v___x_343_ = l_Lean_Meta_mkLambdaFVars(v___x_334_, v_fst_324_, v___x_335_, v___x_298_, v___x_335_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_444_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_444_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_444_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_444_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v_a_299_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
lean_inc_ref(v___x_350_);
v___x_351_ = l_Lean_mkConst(v___x_348_, v___x_350_);
lean_inc_ref(v_binderType_300_);
v___x_352_ = l_Lean_mkApp3(v___x_351_, v_binderType_300_, v_a_342_, v_a_344_);
if (lean_obj_tag(v_fst_328_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_426_; 
lean_del_object(v___x_346_);
v_val_353_ = lean_ctor_get(v_fst_328_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_fst_328_);
if (v_isSharedCheck_426_ == 0)
{
v___x_355_ = v_fst_328_;
v_isShared_356_ = v_isSharedCheck_426_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v_fst_328_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_426_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_mkLambdaFVars(v___x_334_, v___x_308_, v___x_335_, v___x_298_, v___x_335_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = l_Lean_mkAnd(v_fst_320_, v_fst_324_);
lean_inc_ref(v___x_359_);
v___x_360_ = l_Lean_Meta_mkLambdaFVars(v___x_334_, v___x_359_, v___x_335_, v___x_298_, v___x_335_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v___x_362_ = l_Lean_Meta_mkLambdaFVars(v___x_334_, v_val_353_, v___x_335_, v___x_298_, v___x_335_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5));
v___x_365_ = l_Lean_mkConst(v___x_364_, v___x_350_);
v___x_366_ = l_Lean_mkApp4(v___x_365_, v_binderType_300_, v_a_358_, v_a_361_, v_a_363_);
v___x_367_ = l_Lean_Meta_mkForallFVars(v___x_334_, v___x_359_, v___x_335_, v___x_298_, v___x_298_, v___x_336_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec_ref(v___x_334_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_393_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_393_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_393_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_393_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_a_340_);
lean_inc(v_a_338_);
v___x_372_ = l_Lean_mkAnd(v_a_338_, v_a_340_);
v___x_373_ = l_Lean_Meta_mkEqTransCoreProp(v_t_301_, v_a_368_, v___x_372_, v___x_366_, v___x_352_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_373_);
v___x_375_ = v___x_355_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_392_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_box(v___x_298_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_376_);
lean_ctor_set(v___x_330_, 0, v___x_375_);
v___x_378_ = v___x_330_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_391_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_378_);
lean_ctor_set(v___x_326_, 0, v_a_340_);
v___x_380_ = v___x_326_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_340_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_390_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_380_);
lean_ctor_set(v___x_322_, 0, v_a_338_);
v___x_382_ = v___x_322_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_338_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_389_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_382_);
v___x_384_ = v___x_316_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_384_);
v___x_386_ = v___x_370_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
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
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v___x_366_);
lean_del_object(v___x_355_);
lean_dec_ref(v___x_352_);
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_del_object(v___x_330_);
lean_del_object(v___x_326_);
lean_del_object(v___x_322_);
lean_del_object(v___x_316_);
lean_dec_ref(v_t_301_);
v_a_394_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_367_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_367_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_a_361_);
lean_dec_ref(v___x_359_);
lean_dec(v_a_358_);
lean_del_object(v___x_355_);
lean_dec_ref(v___x_352_);
lean_dec_ref_known(v___x_350_, 2);
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_del_object(v___x_326_);
lean_del_object(v___x_322_);
lean_del_object(v___x_316_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
v_a_402_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_362_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_362_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v___x_359_);
lean_dec(v_a_358_);
lean_del_object(v___x_355_);
lean_dec(v_val_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref_known(v___x_350_, 2);
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_del_object(v___x_326_);
lean_del_object(v___x_322_);
lean_del_object(v___x_316_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
v_a_410_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_360_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_360_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_del_object(v___x_355_);
lean_dec(v_val_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref_known(v___x_350_, 2);
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_del_object(v___x_326_);
lean_dec(v_fst_324_);
lean_del_object(v___x_322_);
lean_dec(v_fst_320_);
lean_del_object(v___x_316_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
v_a_418_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_357_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_357_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v___x_428_; 
lean_dec_ref_known(v___x_350_, 2);
lean_dec_ref(v___x_334_);
lean_dec(v_fst_328_);
lean_dec(v_fst_324_);
lean_dec(v_fst_320_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_352_);
v___x_428_ = v___x_316_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_352_);
v___x_428_ = v_reuseFailAlloc_443_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_box(v___x_298_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_429_);
lean_ctor_set(v___x_330_, 0, v___x_428_);
v___x_431_ = v___x_330_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_442_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_431_);
lean_ctor_set(v___x_326_, 0, v_a_340_);
v___x_433_ = v___x_326_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_340_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_441_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_433_);
lean_ctor_set(v___x_322_, 0, v_a_338_);
v___x_435_ = v___x_322_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_338_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_440_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_436_);
v___x_438_ = v___x_346_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
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
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_a_342_);
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_dec(v_fst_328_);
lean_del_object(v___x_326_);
lean_dec(v_fst_324_);
lean_del_object(v___x_322_);
lean_dec(v_fst_320_);
lean_del_object(v___x_316_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
v_a_445_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_343_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_343_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_dec(v_fst_328_);
lean_del_object(v___x_326_);
lean_dec(v_fst_324_);
lean_del_object(v___x_322_);
lean_dec(v_fst_320_);
lean_del_object(v___x_316_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
v_a_453_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_341_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_341_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_338_);
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_dec(v_fst_328_);
lean_del_object(v___x_326_);
lean_dec(v_fst_324_);
lean_del_object(v___x_322_);
lean_dec(v_fst_320_);
lean_del_object(v___x_316_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
v_a_461_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_339_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_339_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v___x_334_);
lean_del_object(v___x_330_);
lean_dec(v_fst_328_);
lean_del_object(v___x_326_);
lean_dec(v_fst_324_);
lean_del_object(v___x_322_);
lean_dec(v_fst_320_);
lean_del_object(v___x_316_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
v_a_469_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_337_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_337_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
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
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_a_310_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_x_302_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
v___x_484_ = lean_box(0);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_484_);
v___x_486_ = v___x_312_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_dec_ref(v___x_308_);
lean_dec_ref(v_x_302_);
lean_dec_ref(v_t_301_);
lean_dec_ref(v_binderType_300_);
lean_dec(v_a_299_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___boxed(lean_object* v_t_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_t_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object* v_e_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_496_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_e_496_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_e_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_552_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_552_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_552_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_552_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
if (lean_obj_tag(v_a_509_) == 1)
{
lean_object* v_val_513_; lean_object* v_snd_514_; lean_object* v_snd_515_; lean_object* v_snd_516_; uint8_t v___x_517_; 
v_val_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_a_509_, 1);
v_snd_514_ = lean_ctor_get(v_val_513_, 1);
lean_inc(v_snd_514_);
v_snd_515_ = lean_ctor_get(v_snd_514_, 1);
lean_inc(v_snd_515_);
v_snd_516_ = lean_ctor_get(v_snd_515_, 1);
v___x_517_ = lean_unbox(v_snd_516_);
if (v___x_517_ == 1)
{
lean_object* v_fst_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_550_; 
v_fst_518_ = lean_ctor_get(v_snd_515_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_snd_515_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_snd_515_, 1);
lean_dec(v_unused_551_);
v___x_520_ = v_snd_515_;
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_fst_518_);
lean_dec(v_snd_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
if (lean_obj_tag(v_fst_518_) == 1)
{
lean_object* v_fst_522_; lean_object* v_fst_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_544_; 
v_fst_522_ = lean_ctor_get(v_val_513_, 0);
lean_inc(v_fst_522_);
lean_dec(v_val_513_);
v_fst_523_ = lean_ctor_get(v_snd_514_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_snd_514_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_snd_514_, 1);
lean_dec(v_unused_545_);
v___x_525_ = v_snd_514_;
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_fst_523_);
lean_dec(v_snd_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_543_; 
v_val_527_ = lean_ctor_get(v_fst_518_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_fst_518_);
if (v_isSharedCheck_543_ == 0)
{
v___x_529_ = v_fst_518_;
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v_fst_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v_val_527_);
lean_ctor_set(v___x_520_, 0, v_fst_523_);
v___x_532_ = v___x_520_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_fst_523_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_val_527_);
v___x_532_ = v_reuseFailAlloc_542_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_532_);
lean_ctor_set(v___x_525_, 0, v_fst_522_);
v___x_534_ = v___x_525_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_fst_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_541_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_534_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_536_);
v___x_538_ = v___x_511_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_548_; 
lean_del_object(v___x_520_);
lean_dec(v_fst_518_);
lean_dec(v_snd_514_);
lean_dec(v_val_513_);
v___x_546_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_546_);
v___x_548_ = v___x_511_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_dec(v_snd_515_);
lean_dec(v_snd_514_);
lean_dec(v_val_513_);
lean_del_object(v___x_511_);
goto v___jp_502_;
}
}
else
{
lean_del_object(v___x_511_);
lean_dec(v_a_509_);
goto v___jp_502_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_508_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_508_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
v___jp_502_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f___boxed(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
}
#ifdef __cplusplus
}
#endif
