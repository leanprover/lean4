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
uint8_t v___x_14_; 
v___x_14_ = l_Lean_Expr_isForall(v_e_13_);
if (v___x_14_ == 0)
{
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_15_ = l_Lean_Expr_getForallBody(v_e_13_);
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = l_Lean_Expr_isAppOfArity(v___x_15_, v___x_16_, v___x_17_);
lean_dec_ref(v___x_15_);
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_e_13_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___boxed(lean_object* v_e_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_20_);
lean_dec_ref(v_e_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(lean_object* v_k_23_, lean_object* v_b_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___x_30_ = lean_apply_6(v_k_23_, v_b_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_31_, lean_object* v_b_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(v_k_31_, v_b_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(lean_object* v_name_39_, uint8_t v_bi_40_, lean_object* v_type_41_, lean_object* v_k_42_, uint8_t v_kind_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_49_, 0, v_k_42_);
v___x_50_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_39_, v_bi_40_, v_type_41_, v___f_49_, v_kind_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_50_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_50_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___boxed(lean_object* v_name_67_, lean_object* v_bi_68_, lean_object* v_type_69_, lean_object* v_k_70_, lean_object* v_kind_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
uint8_t v_bi_boxed_77_; uint8_t v_kind_boxed_78_; lean_object* v_res_79_; 
v_bi_boxed_77_ = lean_unbox(v_bi_68_);
v_kind_boxed_78_ = lean_unbox(v_kind_71_);
v_res_79_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_67_, v_bi_boxed_77_, v_type_69_, v_k_70_, v_kind_boxed_78_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(lean_object* v_00_u03b1_80_, lean_object* v_name_81_, uint8_t v_bi_82_, lean_object* v_type_83_, lean_object* v_k_84_, uint8_t v_kind_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_81_, v_bi_82_, v_type_83_, v_k_84_, v_kind_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_92_, lean_object* v_name_93_, lean_object* v_bi_94_, lean_object* v_type_95_, lean_object* v_k_96_, lean_object* v_kind_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v_bi_boxed_103_; uint8_t v_kind_boxed_104_; lean_object* v_res_105_; 
v_bi_boxed_103_ = lean_unbox(v_bi_94_);
v_kind_boxed_104_ = lean_unbox(v_kind_97_);
v_res_105_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(v_00_u03b1_92_, v_name_93_, v_bi_boxed_103_, v_type_95_, v_k_96_, v_kind_boxed_104_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = l_Lean_Level_ofNat(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed(lean_object* v_body_124_, lean_object* v___x_125_, lean_object* v_a_126_, lean_object* v_binderType_127_, lean_object* v_t_128_, lean_object* v_x_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v___x_4230__boxed_135_; lean_object* v_res_136_; 
v___x_4230__boxed_135_ = lean_unbox(v___x_125_);
v_res_136_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(v_body_124_, v___x_4230__boxed_135_, v_a_126_, v_binderType_127_, v_t_128_, v_x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec_ref(v_body_124_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(lean_object* v_t_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___x_265_; 
lean_inc_ref(v_t_141_);
v___x_265_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_141_, v_a_143_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_286_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_286_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_286_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_286_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = l_Lean_Expr_cleanupAnnotations(v_a_266_);
v___x_271_ = l_Lean_Expr_isApp(v___x_270_);
if (v___x_271_ == 0)
{
lean_dec_ref(v___x_270_);
lean_del_object(v___x_268_);
v___y_148_ = v_a_142_;
v___y_149_ = v_a_143_;
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
goto v___jp_147_;
}
else
{
lean_object* v_arg_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_arg_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc_ref(v_arg_272_);
v___x_273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_270_);
v___x_274_ = l_Lean_Expr_isApp(v___x_273_);
if (v___x_274_ == 0)
{
lean_dec_ref(v___x_273_);
lean_dec_ref(v_arg_272_);
lean_del_object(v___x_268_);
v___y_148_ = v_a_142_;
v___y_149_ = v_a_143_;
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
goto v___jp_147_;
}
else
{
lean_object* v_arg_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_arg_275_ = lean_ctor_get(v___x_273_, 1);
lean_inc_ref(v_arg_275_);
v___x_276_ = l_Lean_Expr_appFnCleanup___redArg(v___x_273_);
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_278_ = l_Lean_Expr_isConstOf(v___x_276_, v___x_277_);
lean_dec_ref(v___x_276_);
if (v___x_278_ == 0)
{
lean_dec_ref(v_arg_275_);
lean_dec_ref(v_arg_272_);
lean_del_object(v___x_268_);
v___y_148_ = v_a_142_;
v___y_149_ = v_a_143_;
v___y_150_ = v_a_144_;
v___y_151_ = v_a_145_;
goto v___jp_147_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec_ref(v_t_141_);
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4));
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_arg_272_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_arg_275_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_282_);
v___x_284_ = v___x_268_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_t_141_);
v_a_287_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_265_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_265_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
v___jp_147_:
{
if (lean_obj_tag(v_t_141_) == 7)
{
lean_object* v_binderName_152_; lean_object* v_binderType_153_; lean_object* v_body_154_; uint8_t v_binderInfo_155_; lean_object* v___x_156_; 
v_binderName_152_ = lean_ctor_get(v_t_141_, 0);
v_binderType_153_ = lean_ctor_get(v_t_141_, 1);
v_body_154_ = lean_ctor_get(v_t_141_, 2);
v_binderInfo_155_ = lean_ctor_get_uint8(v_t_141_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_153_);
v___x_156_ = l_Lean_Meta_getLevel(v_binderType_153_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; uint8_t v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l_Lean_Expr_hasLooseBVars(v_body_154_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_inc_ref(v_body_154_);
v___x_159_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_body_154_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_250_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_250_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_250_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_250_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
if (lean_obj_tag(v_a_160_) == 1)
{
lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_245_; 
v_val_164_ = lean_ctor_get(v_a_160_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_245_ == 0)
{
v___x_166_ = v_a_160_;
v_isShared_167_ = v_isSharedCheck_245_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_dec(v_a_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_245_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_snd_168_; lean_object* v_snd_169_; lean_object* v_fst_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_243_; 
v_snd_168_ = lean_ctor_get(v_val_164_, 1);
lean_inc(v_snd_168_);
v_snd_169_ = lean_ctor_get(v_snd_168_, 1);
lean_inc(v_snd_169_);
v_fst_170_ = lean_ctor_get(v_val_164_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_val_164_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_val_164_, 1);
lean_dec(v_unused_244_);
v___x_172_ = v_val_164_;
v_isShared_173_ = v_isSharedCheck_243_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_fst_170_);
lean_dec(v_val_164_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_243_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_fst_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_241_; 
v_fst_174_ = lean_ctor_get(v_snd_168_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_snd_168_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_snd_168_, 1);
lean_dec(v_unused_242_);
v___x_176_ = v_snd_168_;
v_isShared_177_ = v_isSharedCheck_241_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_fst_174_);
lean_dec(v_snd_168_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_241_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_240_; 
v_fst_178_ = lean_ctor_get(v_snd_169_, 0);
v_snd_179_ = lean_ctor_get(v_snd_169_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_snd_169_);
if (v_isSharedCheck_240_ == 0)
{
v___x_181_ = v_snd_169_;
v_isShared_182_ = v_isSharedCheck_240_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_inc(v_fst_178_);
lean_dec(v_snd_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_240_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc_n(v_fst_170_, 2);
lean_inc_ref_n(v_binderType_153_, 5);
lean_inc_n(v_binderName_152_, 4);
v___x_183_ = l_Lean_mkForall(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v_fst_170_);
lean_inc_n(v_fst_174_, 2);
v___x_184_ = l_Lean_mkForall(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v_fst_174_);
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_186_ = lean_box(0);
lean_inc(v_a_157_);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v_a_157_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = l_Lean_mkConst(v___x_185_, v___x_187_);
v___x_189_ = l_Lean_mkLambda(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v_fst_170_);
v___x_190_ = l_Lean_mkLambda(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v_fst_174_);
v___x_191_ = l_Lean_mkApp3(v___x_188_, v_binderType_153_, v___x_189_, v___x_190_);
if (lean_obj_tag(v_fst_178_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_223_; 
v_val_192_ = lean_ctor_get(v_fst_178_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_fst_178_);
if (v_isSharedCheck_223_ == 0)
{
v___x_194_ = v_fst_178_;
v_isShared_195_ = v_isSharedCheck_223_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v_fst_178_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_223_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1));
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v_a_157_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_mkConst(v___x_196_, v___x_198_);
v___x_200_ = l_Lean_mkAnd(v_fst_170_, v_fst_174_);
lean_inc_ref(v___x_200_);
lean_inc_ref(v_body_154_);
lean_inc_ref_n(v_binderType_153_, 2);
v___x_201_ = l_Lean_mkApp4(v___x_199_, v_binderType_153_, v_body_154_, v___x_200_, v_val_192_);
lean_inc(v_binderName_152_);
v___x_202_ = l_Lean_mkForall(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v___x_200_);
lean_inc_ref(v___x_184_);
lean_inc_ref(v___x_183_);
v___x_203_ = l_Lean_mkAnd(v___x_183_, v___x_184_);
v___x_204_ = l_Lean_Meta_mkEqTransCoreProp(v_t_141_, v___x_202_, v___x_203_, v___x_201_, v___x_191_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_204_);
v___x_206_ = v___x_194_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_222_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_206_);
v___x_208_ = v___x_181_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_snd_179_);
v___x_208_ = v_reuseFailAlloc_221_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_208_);
lean_ctor_set(v___x_176_, 0, v___x_184_);
v___x_210_ = v___x_176_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_220_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_210_);
lean_ctor_set(v___x_172_, 0, v___x_183_);
v___x_212_ = v___x_172_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_219_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_212_);
v___x_214_ = v___x_166_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_214_);
v___x_216_ = v___x_162_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
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
}
}
}
}
else
{
lean_object* v___x_225_; 
lean_dec(v_fst_178_);
lean_dec(v_fst_174_);
lean_dec(v_fst_170_);
lean_dec(v_a_157_);
lean_dec_ref_known(v_t_141_, 3);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_191_);
v___x_225_ = v___x_166_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_191_);
v___x_225_ = v_reuseFailAlloc_239_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_225_);
v___x_227_ = v___x_181_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_snd_179_);
v___x_227_ = v_reuseFailAlloc_238_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_227_);
lean_ctor_set(v___x_176_, 0, v___x_184_);
v___x_229_ = v___x_176_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_237_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_229_);
lean_ctor_set(v___x_172_, 0, v___x_183_);
v___x_231_ = v___x_172_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_236_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_232_);
v___x_234_ = v___x_162_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
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
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec(v_a_160_);
lean_dec(v_a_157_);
lean_dec_ref_known(v_t_141_, 3);
v___x_246_ = lean_box(0);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_246_);
v___x_248_ = v___x_162_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_dec(v_a_157_);
lean_dec_ref_known(v_t_141_, 3);
return v___x_159_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___f_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
lean_inc_ref(v_body_154_);
lean_inc_ref_n(v_binderType_153_, 2);
lean_inc(v_binderName_152_);
v___x_251_ = lean_box(v___x_158_);
v___f_252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed), 11, 5);
lean_closure_set(v___f_252_, 0, v_body_154_);
lean_closure_set(v___f_252_, 1, v___x_251_);
lean_closure_set(v___f_252_, 2, v_a_157_);
lean_closure_set(v___f_252_, 3, v_binderType_153_);
lean_closure_set(v___f_252_, 4, v_t_141_);
v___x_253_ = 0;
v___x_254_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_binderName_152_, v_binderInfo_155_, v_binderType_153_, v___f_252_, v___x_253_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
return v___x_254_;
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref_known(v_t_141_, 3);
v_a_255_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_156_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_156_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_t_141_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(lean_object* v_body_295_, uint8_t v___x_296_, lean_object* v_a_297_, lean_object* v_binderType_298_, lean_object* v_t_299_, lean_object* v_x_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_expr_instantiate1(v_body_295_, v_x_300_);
lean_inc_ref(v___x_306_);
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v___x_306_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_486_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_486_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_486_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_486_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
if (lean_obj_tag(v_a_308_) == 1)
{
lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_310_);
v_val_312_ = lean_ctor_get(v_a_308_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_481_ == 0)
{
v___x_314_ = v_a_308_;
v_isShared_315_ = v_isSharedCheck_481_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v_a_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_481_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_snd_316_; lean_object* v_snd_317_; lean_object* v_fst_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_479_; 
v_snd_316_ = lean_ctor_get(v_val_312_, 1);
lean_inc(v_snd_316_);
v_snd_317_ = lean_ctor_get(v_snd_316_, 1);
lean_inc(v_snd_317_);
v_fst_318_ = lean_ctor_get(v_val_312_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_val_312_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_val_312_, 1);
lean_dec(v_unused_480_);
v___x_320_ = v_val_312_;
v_isShared_321_ = v_isSharedCheck_479_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_fst_318_);
lean_dec(v_val_312_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_479_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_fst_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_477_; 
v_fst_322_ = lean_ctor_get(v_snd_316_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_snd_316_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_snd_316_, 1);
lean_dec(v_unused_478_);
v___x_324_ = v_snd_316_;
v_isShared_325_ = v_isSharedCheck_477_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_fst_322_);
lean_dec(v_snd_316_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_477_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_fst_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_475_; 
v_fst_326_ = lean_ctor_get(v_snd_317_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_snd_317_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_snd_317_, 1);
lean_dec(v_unused_476_);
v___x_328_ = v_snd_317_;
v_isShared_329_ = v_isSharedCheck_475_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_fst_326_);
lean_dec(v_snd_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_475_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_array_push(v___x_331_, v_x_300_);
v___x_333_ = 0;
v___x_334_ = 1;
lean_inc(v_fst_318_);
v___x_335_ = l_Lean_Meta_mkForallFVars(v___x_332_, v_fst_318_, v___x_333_, v___x_296_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
lean_inc(v_fst_322_);
v___x_337_ = l_Lean_Meta_mkForallFVars(v___x_332_, v_fst_322_, v___x_333_, v___x_296_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
lean_inc(v_fst_318_);
v___x_339_ = l_Lean_Meta_mkLambdaFVars(v___x_332_, v_fst_318_, v___x_333_, v___x_296_, v___x_333_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
lean_inc(v_fst_322_);
v___x_341_ = l_Lean_Meta_mkLambdaFVars(v___x_332_, v_fst_322_, v___x_333_, v___x_296_, v___x_333_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_442_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_442_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_442_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_442_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v_a_297_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_inc_ref(v___x_348_);
v___x_349_ = l_Lean_mkConst(v___x_346_, v___x_348_);
lean_inc_ref(v_binderType_298_);
v___x_350_ = l_Lean_mkApp3(v___x_349_, v_binderType_298_, v_a_340_, v_a_342_);
if (lean_obj_tag(v_fst_326_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_424_; 
lean_del_object(v___x_344_);
v_val_351_ = lean_ctor_get(v_fst_326_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_fst_326_);
if (v_isSharedCheck_424_ == 0)
{
v___x_353_ = v_fst_326_;
v_isShared_354_ = v_isSharedCheck_424_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_val_351_);
lean_dec(v_fst_326_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_424_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_mkLambdaFVars(v___x_332_, v___x_306_, v___x_333_, v___x_296_, v___x_333_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = l_Lean_mkAnd(v_fst_318_, v_fst_322_);
lean_inc_ref(v___x_357_);
v___x_358_ = l_Lean_Meta_mkLambdaFVars(v___x_332_, v___x_357_, v___x_333_, v___x_296_, v___x_333_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = l_Lean_Meta_mkLambdaFVars(v___x_332_, v_val_351_, v___x_333_, v___x_296_, v___x_333_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5));
v___x_363_ = l_Lean_mkConst(v___x_362_, v___x_348_);
v___x_364_ = l_Lean_mkApp4(v___x_363_, v_binderType_298_, v_a_356_, v_a_359_, v_a_361_);
v___x_365_ = l_Lean_Meta_mkForallFVars(v___x_332_, v___x_357_, v___x_333_, v___x_296_, v___x_296_, v___x_334_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_391_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_391_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_391_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_391_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_inc(v_a_338_);
lean_inc(v_a_336_);
v___x_370_ = l_Lean_mkAnd(v_a_336_, v_a_338_);
v___x_371_ = l_Lean_Meta_mkEqTransCoreProp(v_t_299_, v_a_366_, v___x_370_, v___x_364_, v___x_350_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_371_);
v___x_373_ = v___x_353_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_390_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_296_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_374_);
lean_ctor_set(v___x_328_, 0, v___x_373_);
v___x_376_ = v___x_328_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_389_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_376_);
lean_ctor_set(v___x_324_, 0, v_a_338_);
v___x_378_ = v___x_324_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_338_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_388_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_378_);
lean_ctor_set(v___x_320_, 0, v_a_336_);
v___x_380_ = v___x_320_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_387_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_380_);
v___x_382_ = v___x_314_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_382_);
v___x_384_ = v___x_368_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
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
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v___x_364_);
lean_del_object(v___x_353_);
lean_dec_ref(v___x_350_);
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_del_object(v___x_328_);
lean_del_object(v___x_324_);
lean_del_object(v___x_320_);
lean_del_object(v___x_314_);
lean_dec_ref(v_t_299_);
v_a_392_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_365_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_365_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_a_359_);
lean_dec_ref(v___x_357_);
lean_dec(v_a_356_);
lean_del_object(v___x_353_);
lean_dec_ref(v___x_350_);
lean_dec_ref_known(v___x_348_, 2);
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_324_);
lean_del_object(v___x_320_);
lean_del_object(v___x_314_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
v_a_400_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_360_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_360_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v___x_357_);
lean_dec(v_a_356_);
lean_del_object(v___x_353_);
lean_dec(v_val_351_);
lean_dec_ref(v___x_350_);
lean_dec_ref_known(v___x_348_, 2);
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_324_);
lean_del_object(v___x_320_);
lean_del_object(v___x_314_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
v_a_408_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_358_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_358_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_del_object(v___x_353_);
lean_dec(v_val_351_);
lean_dec_ref(v___x_350_);
lean_dec_ref_known(v___x_348_, 2);
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_324_);
lean_dec(v_fst_322_);
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_del_object(v___x_314_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
v_a_416_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_355_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_355_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v___x_426_; 
lean_dec_ref_known(v___x_348_, 2);
lean_dec_ref(v___x_332_);
lean_dec(v_fst_326_);
lean_dec(v_fst_322_);
lean_dec(v_fst_318_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_350_);
v___x_426_ = v___x_314_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_350_);
v___x_426_ = v_reuseFailAlloc_441_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_box(v___x_296_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_427_);
lean_ctor_set(v___x_328_, 0, v___x_426_);
v___x_429_ = v___x_328_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_440_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_429_);
lean_ctor_set(v___x_324_, 0, v_a_338_);
v___x_431_ = v___x_324_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_338_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_439_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_431_);
lean_ctor_set(v___x_320_, 0, v_a_336_);
v___x_433_ = v___x_320_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_438_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_434_);
v___x_436_ = v___x_344_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
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
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_a_340_);
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_324_);
lean_dec(v_fst_322_);
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_del_object(v___x_314_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
v_a_443_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_341_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_341_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_338_);
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_324_);
lean_dec(v_fst_322_);
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_del_object(v___x_314_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
v_a_451_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_339_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_339_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_324_);
lean_dec(v_fst_322_);
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_del_object(v___x_314_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
v_a_459_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_337_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_337_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v___x_332_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_324_);
lean_dec(v_fst_322_);
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_del_object(v___x_314_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
v_a_467_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_335_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_335_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
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
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec(v_a_308_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
v___x_482_ = lean_box(0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_482_);
v___x_484_ = v___x_310_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_dec_ref(v___x_306_);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_t_299_);
lean_dec_ref(v_binderType_298_);
lean_dec(v_a_297_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___boxed(lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_t_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object* v_e_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_494_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_e_494_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_e_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_550_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_550_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_550_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_550_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
if (lean_obj_tag(v_a_507_) == 1)
{
lean_object* v_val_511_; lean_object* v_snd_512_; lean_object* v_snd_513_; lean_object* v_snd_514_; uint8_t v___x_515_; 
v_val_511_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_a_507_, 1);
v_snd_512_ = lean_ctor_get(v_val_511_, 1);
lean_inc(v_snd_512_);
v_snd_513_ = lean_ctor_get(v_snd_512_, 1);
lean_inc(v_snd_513_);
v_snd_514_ = lean_ctor_get(v_snd_513_, 1);
v___x_515_ = lean_unbox(v_snd_514_);
if (v___x_515_ == 1)
{
lean_object* v_fst_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_548_; 
v_fst_516_ = lean_ctor_get(v_snd_513_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_513_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_snd_513_, 1);
lean_dec(v_unused_549_);
v___x_518_ = v_snd_513_;
v_isShared_519_ = v_isSharedCheck_548_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_fst_516_);
lean_dec(v_snd_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_548_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_fst_516_) == 1)
{
lean_object* v_fst_520_; lean_object* v_fst_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_542_; 
v_fst_520_ = lean_ctor_get(v_val_511_, 0);
lean_inc(v_fst_520_);
lean_dec(v_val_511_);
v_fst_521_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_snd_512_, 1);
lean_dec(v_unused_543_);
v___x_523_ = v_snd_512_;
v_isShared_524_ = v_isSharedCheck_542_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_fst_521_);
lean_dec(v_snd_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_542_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_541_; 
v_val_525_ = lean_ctor_get(v_fst_516_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_fst_516_);
if (v_isSharedCheck_541_ == 0)
{
v___x_527_ = v_fst_516_;
v_isShared_528_ = v_isSharedCheck_541_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v_fst_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_541_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v_val_525_);
lean_ctor_set(v___x_518_, 0, v_fst_521_);
v___x_530_ = v___x_518_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_521_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_val_525_);
v___x_530_ = v_reuseFailAlloc_540_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_530_);
lean_ctor_set(v___x_523_, 0, v_fst_520_);
v___x_532_ = v___x_523_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_539_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_532_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_534_);
v___x_536_ = v___x_509_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
lean_del_object(v___x_518_);
lean_dec(v_fst_516_);
lean_dec(v_snd_512_);
lean_dec(v_val_511_);
v___x_544_ = lean_box(0);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_544_);
v___x_546_ = v___x_509_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_dec(v_snd_513_);
lean_dec(v_snd_512_);
lean_dec(v_val_511_);
lean_del_object(v___x_509_);
goto v___jp_500_;
}
}
else
{
lean_del_object(v___x_509_);
lean_dec(v_a_507_);
goto v___jp_500_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_506_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_506_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f___boxed(lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_565_;
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
