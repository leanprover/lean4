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
uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(lean_object* v_a_1_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
uint8_t v_res_7_;
v_res_7_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_a_1_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder___boxed(lean_object* v_a_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_a_8_);
lean_dec_ref(v_a_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(lean_object* v_e_14_){
_start:
{
uint8_t v___y_16_; uint8_t v___x_18_; 
v___x_18_ = l_Lean_Expr_isForall(v_e_14_);
if (v___x_18_ == 0)
{
v___y_16_ = v___x_18_;
goto v___jp_15_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_19_ = l_Lean_Expr_getForallBody(v_e_14_);
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = l_Lean_Expr_isAppOfArity(v___x_19_, v___x_20_, v___x_21_);
lean_dec_ref(v___x_19_);
v___y_16_ = v___x_22_;
goto v___jp_15_;
}
v___jp_15_:
{
if (v___y_16_ == 0)
{
return v___y_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_hasDepBinder(v_e_14_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_14_ = stack[0].m_obj;
uint8_t v_res_23_;
v_res_23_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_14_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___boxed(lean_object* v_e_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_24_);
lean_dec_ref(v_e_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(lean_object* v_k_27_, lean_object* v_b_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
v___x_34_ = lean_apply_6(v_k_27_, v_b_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, lean_box(0));
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_27_ = stack[0].m_obj;
lean_object* v_b_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v___y_32_ = stack[5].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(v_k_27_, v_b_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_36_, lean_object* v_b_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0(v_k_36_, v_b_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(lean_object* v_name_44_, uint8_t v_bi_45_, lean_object* v_type_46_, lean_object* v_k_47_, uint8_t v_kind_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; 
v___f_54_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_54_, 0, v_k_47_);
v___x_55_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_44_, v_bi_45_, v_type_46_, v___f_54_, v_kind_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_64_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_55_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_55_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_44_ = stack[0].m_obj;
uint8_t v_bi_45_ = stack[1].m_num;
lean_object* v_type_46_ = stack[2].m_obj;
lean_object* v_k_47_ = stack[3].m_obj;
uint8_t v_kind_48_ = stack[4].m_num;
lean_object* v___y_49_ = stack[5].m_obj;
lean_object* v___y_50_ = stack[6].m_obj;
lean_object* v___y_51_ = stack[7].m_obj;
lean_object* v___y_52_ = stack[8].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_44_, v_bi_45_, v_type_46_, v_k_47_, v_kind_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg___boxed(lean_object* v_name_73_, lean_object* v_bi_74_, lean_object* v_type_75_, lean_object* v_k_76_, lean_object* v_kind_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_bi_boxed_83_; uint8_t v_kind_boxed_84_; lean_object* v_res_85_; 
v_bi_boxed_83_ = lean_unbox(v_bi_74_);
v_kind_boxed_84_ = lean_unbox(v_kind_77_);
v_res_85_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_73_, v_bi_boxed_83_, v_type_75_, v_k_76_, v_kind_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(lean_object* v_00_u03b1_86_, lean_object* v_name_87_, uint8_t v_bi_88_, lean_object* v_type_89_, lean_object* v_k_90_, uint8_t v_kind_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_name_87_, v_bi_88_, v_type_89_, v_k_90_, v_kind_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_87_ = stack[1].m_obj;
uint8_t v_bi_88_ = stack[2].m_num;
lean_object* v_type_89_ = stack[3].m_obj;
lean_object* v_k_90_ = stack[4].m_obj;
uint8_t v_kind_91_ = stack[5].m_num;
lean_object* v___y_92_ = stack[6].m_obj;
lean_object* v___y_93_ = stack[7].m_obj;
lean_object* v___y_94_ = stack[8].m_obj;
lean_object* v___y_95_ = stack[9].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(lean_box(0), v_name_87_, v_bi_88_, v_type_89_, v_k_90_, v_kind_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_99_, lean_object* v_name_100_, lean_object* v_bi_101_, lean_object* v_type_102_, lean_object* v_k_103_, lean_object* v_kind_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
uint8_t v_bi_boxed_110_; uint8_t v_kind_boxed_111_; lean_object* v_res_112_; 
v_bi_boxed_110_ = lean_unbox(v_bi_101_);
v_kind_boxed_111_ = lean_unbox(v_kind_104_);
v_res_112_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0(v_00_u03b1_99_, v_name_100_, v_bi_boxed_110_, v_type_102_, v_k_103_, v_kind_boxed_111_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l_Lean_Level_ofNat(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_box(0);
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__2);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed(lean_object* v_body_131_, lean_object* v___x_132_, lean_object* v_a_133_, lean_object* v_binderType_134_, lean_object* v_t_135_, lean_object* v_x_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v___x_4280__boxed_142_; lean_object* v_res_143_; 
v___x_4280__boxed_142_ = lean_unbox(v___x_132_);
v_res_143_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(v_body_131_, v___x_4280__boxed_142_, v_a_133_, v_binderType_134_, v_t_135_, v_x_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec_ref(v_body_131_);
return v_res_143_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(lean_object* v_t_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___x_272_; 
lean_inc_ref(v_t_148_);
v___x_272_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_148_, v_a_150_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_293_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_293_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_Expr_cleanupAnnotations(v_a_273_);
v___x_278_ = l_Lean_Expr_isApp(v___x_277_);
if (v___x_278_ == 0)
{
lean_dec_ref(v___x_277_);
lean_del_object(v___x_275_);
v___y_155_ = v_a_149_;
v___y_156_ = v_a_150_;
v___y_157_ = v_a_151_;
v___y_158_ = v_a_152_;
goto v___jp_154_;
}
else
{
lean_object* v_arg_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_arg_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc_ref(v_arg_279_);
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_277_);
v___x_281_ = l_Lean_Expr_isApp(v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v_arg_279_);
lean_del_object(v___x_275_);
v___y_155_ = v_a_149_;
v___y_156_ = v_a_150_;
v___y_157_ = v_a_151_;
v___y_158_ = v_a_152_;
goto v___jp_154_;
}
else
{
lean_object* v_arg_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_arg_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc_ref(v_arg_282_);
v___x_283_ = l_Lean_Expr_appFnCleanup___redArg(v___x_280_);
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate___closed__1));
v___x_285_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_284_);
lean_dec_ref(v___x_283_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_arg_282_);
lean_dec_ref(v_arg_279_);
lean_del_object(v___x_275_);
v___y_155_ = v_a_149_;
v___y_156_ = v_a_150_;
v___y_157_ = v_a_151_;
v___y_158_ = v_a_152_;
goto v___jp_154_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec_ref(v_t_148_);
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__4));
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_arg_279_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_arg_282_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_289_);
v___x_291_ = v___x_275_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_t_148_);
v_a_294_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_272_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_272_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
v___jp_154_:
{
if (lean_obj_tag(v_t_148_) == 7)
{
lean_object* v_binderName_159_; lean_object* v_binderType_160_; lean_object* v_body_161_; uint8_t v_binderInfo_162_; lean_object* v___x_163_; 
v_binderName_159_ = lean_ctor_get(v_t_148_, 0);
v_binderType_160_ = lean_ctor_get(v_t_148_, 1);
v_body_161_ = lean_ctor_get(v_t_148_, 2);
v_binderInfo_162_ = lean_ctor_get_uint8(v_t_148_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_160_);
v___x_163_ = l_Lean_Meta_getLevel(v_binderType_160_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; uint8_t v___x_165_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = l_Lean_Expr_hasLooseBVars(v_body_161_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_inc_ref(v_body_161_);
v___x_166_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_body_161_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_257_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_257_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_257_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_257_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
if (lean_obj_tag(v_a_167_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_252_; 
v_val_171_ = lean_ctor_get(v_a_167_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_252_ == 0)
{
v___x_173_ = v_a_167_;
v_isShared_174_ = v_isSharedCheck_252_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v_a_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_252_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_snd_175_; lean_object* v_snd_176_; lean_object* v_fst_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_250_; 
v_snd_175_ = lean_ctor_get(v_val_171_, 1);
lean_inc(v_snd_175_);
v_snd_176_ = lean_ctor_get(v_snd_175_, 1);
lean_inc(v_snd_176_);
v_fst_177_ = lean_ctor_get(v_val_171_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_val_171_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_val_171_, 1);
lean_dec(v_unused_251_);
v___x_179_ = v_val_171_;
v_isShared_180_ = v_isSharedCheck_250_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_fst_177_);
lean_dec(v_val_171_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_250_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_fst_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_248_; 
v_fst_181_ = lean_ctor_get(v_snd_175_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_snd_175_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_snd_175_, 1);
lean_dec(v_unused_249_);
v___x_183_ = v_snd_175_;
v_isShared_184_ = v_isSharedCheck_248_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_fst_181_);
lean_dec(v_snd_175_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_248_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_247_; 
v_fst_185_ = lean_ctor_get(v_snd_176_, 0);
v_snd_186_ = lean_ctor_get(v_snd_176_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_snd_176_);
if (v_isSharedCheck_247_ == 0)
{
v___x_188_ = v_snd_176_;
v_isShared_189_ = v_isSharedCheck_247_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
lean_dec(v_snd_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_247_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_inc_n(v_fst_177_, 2);
lean_inc_ref_n(v_binderType_160_, 5);
lean_inc_n(v_binderName_159_, 4);
v___x_190_ = l_Lean_mkForall(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v_fst_177_);
lean_inc_n(v_fst_181_, 2);
v___x_191_ = l_Lean_mkForall(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v_fst_181_);
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_193_ = lean_box(0);
lean_inc(v_a_164_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v_a_164_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = l_Lean_mkConst(v___x_192_, v___x_194_);
v___x_196_ = l_Lean_mkLambda(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v_fst_177_);
v___x_197_ = l_Lean_mkLambda(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v_fst_181_);
v___x_198_ = l_Lean_mkApp3(v___x_195_, v_binderType_160_, v___x_196_, v___x_197_);
if (lean_obj_tag(v_fst_185_) == 1)
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_230_; 
v_val_199_ = lean_ctor_get(v_fst_185_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_fst_185_);
if (v_isSharedCheck_230_ == 0)
{
v___x_201_ = v_fst_185_;
v_isShared_202_ = v_isSharedCheck_230_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v_fst_185_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_230_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__1));
v___x_204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___closed__3);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v_a_164_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = l_Lean_mkConst(v___x_203_, v___x_205_);
v___x_207_ = l_Lean_mkAnd(v_fst_177_, v_fst_181_);
lean_inc_ref(v___x_207_);
lean_inc_ref(v_body_161_);
lean_inc_ref_n(v_binderType_160_, 2);
v___x_208_ = l_Lean_mkApp4(v___x_206_, v_binderType_160_, v_body_161_, v___x_207_, v_val_199_);
lean_inc(v_binderName_159_);
v___x_209_ = l_Lean_mkForall(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v___x_207_);
lean_inc_ref(v___x_191_);
lean_inc_ref(v___x_190_);
v___x_210_ = l_Lean_mkAnd(v___x_190_, v___x_191_);
v___x_211_ = l_Lean_Meta_mkEqTransCoreProp(v_t_148_, v___x_209_, v___x_210_, v___x_208_, v___x_198_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_211_);
v___x_213_ = v___x_201_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_229_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_213_);
v___x_215_ = v___x_188_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_snd_186_);
v___x_215_ = v_reuseFailAlloc_228_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_215_);
lean_ctor_set(v___x_183_, 0, v___x_191_);
v___x_217_ = v___x_183_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_227_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_217_);
lean_ctor_set(v___x_179_, 0, v___x_190_);
v___x_219_ = v___x_179_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_226_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_219_);
v___x_221_ = v___x_173_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_221_);
v___x_223_ = v___x_169_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
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
else
{
lean_object* v___x_232_; 
lean_dec(v_fst_185_);
lean_dec(v_fst_181_);
lean_dec(v_fst_177_);
lean_dec(v_a_164_);
lean_dec_ref_known(v_t_148_, 3);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_198_);
v___x_232_ = v___x_173_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_198_);
v___x_232_ = v_reuseFailAlloc_246_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_232_);
v___x_234_ = v___x_188_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_snd_186_);
v___x_234_ = v_reuseFailAlloc_245_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_234_);
lean_ctor_set(v___x_183_, 0, v___x_191_);
v___x_236_ = v___x_183_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_244_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_236_);
lean_ctor_set(v___x_179_, 0, v___x_190_);
v___x_238_ = v___x_179_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_239_);
v___x_241_ = v___x_169_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
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
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_a_167_);
lean_dec(v_a_164_);
lean_dec_ref_known(v_t_148_, 3);
v___x_253_ = lean_box(0);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_253_);
v___x_255_ = v___x_169_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_dec(v_a_164_);
lean_dec_ref_known(v_t_148_, 3);
return v___x_166_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___f_259_; uint8_t v___x_260_; lean_object* v___x_261_; 
lean_inc_ref(v_body_161_);
lean_inc_ref_n(v_binderType_160_, 2);
lean_inc(v_binderName_159_);
v___x_258_ = lean_box(v___x_165_);
v___f_259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___boxed), 11, 5);
lean_closure_set(v___f_259_, 0, v_body_161_);
lean_closure_set(v___f_259_, 1, v___x_258_);
lean_closure_set(v___f_259_, 2, v_a_164_);
lean_closure_set(v___f_259_, 3, v_binderType_160_);
lean_closure_set(v___f_259_, 4, v_t_148_);
v___x_260_ = 0;
v___x_261_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_spec__0___redArg(v_binderName_159_, v_binderInfo_162_, v_binderType_160_, v___f_259_, v___x_260_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
return v___x_261_;
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref_known(v_t_148_, 3);
v_a_262_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_163_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_163_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_t_148_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_148_ = stack[0].m_obj;
lean_object* v_a_149_ = stack[1].m_obj;
lean_object* v_a_150_ = stack[2].m_obj;
lean_object* v_a_151_ = stack[3].m_obj;
lean_object* v_a_152_ = stack[4].m_obj;
lean_object* v_res_302_;
v_res_302_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_t_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_302_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(lean_object* v_body_303_, uint8_t v___x_304_, lean_object* v_a_305_, lean_object* v_binderType_306_, lean_object* v_t_307_, lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_expr_instantiate1(v_body_303_, v_x_308_);
lean_inc_ref(v___x_314_);
v___x_315_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v___x_314_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_494_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_494_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_494_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_494_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
if (lean_obj_tag(v_a_316_) == 1)
{
lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_489_; 
lean_del_object(v___x_318_);
v_val_320_ = lean_ctor_get(v_a_316_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_489_ == 0)
{
v___x_322_ = v_a_316_;
v_isShared_323_ = v_isSharedCheck_489_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_dec(v_a_316_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_489_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_snd_324_; lean_object* v_snd_325_; lean_object* v_fst_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_487_; 
v_snd_324_ = lean_ctor_get(v_val_320_, 1);
lean_inc(v_snd_324_);
v_snd_325_ = lean_ctor_get(v_snd_324_, 1);
lean_inc(v_snd_325_);
v_fst_326_ = lean_ctor_get(v_val_320_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_val_320_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_val_320_, 1);
lean_dec(v_unused_488_);
v___x_328_ = v_val_320_;
v_isShared_329_ = v_isSharedCheck_487_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_fst_326_);
lean_dec(v_val_320_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_487_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fst_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_485_; 
v_fst_330_ = lean_ctor_get(v_snd_324_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_snd_324_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_snd_324_, 1);
lean_dec(v_unused_486_);
v___x_332_ = v_snd_324_;
v_isShared_333_ = v_isSharedCheck_485_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_fst_330_);
lean_dec(v_snd_324_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_485_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fst_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_483_; 
v_fst_334_ = lean_ctor_get(v_snd_325_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_snd_325_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_snd_325_, 1);
lean_dec(v_unused_484_);
v___x_336_ = v_snd_325_;
v_isShared_337_ = v_isSharedCheck_483_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_fst_334_);
lean_dec(v_snd_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_483_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_array_push(v___x_339_, v_x_308_);
v___x_341_ = 0;
v___x_342_ = 1;
lean_inc(v_fst_326_);
v___x_343_ = l_Lean_Meta_mkForallFVars(v___x_340_, v_fst_326_, v___x_341_, v___x_304_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
lean_inc(v_fst_330_);
v___x_345_ = l_Lean_Meta_mkForallFVars(v___x_340_, v_fst_330_, v___x_341_, v___x_304_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
lean_inc(v_fst_326_);
v___x_347_ = l_Lean_Meta_mkLambdaFVars(v___x_340_, v_fst_326_, v___x_341_, v___x_304_, v___x_341_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
lean_inc(v_fst_330_);
v___x_349_ = l_Lean_Meta_mkLambdaFVars(v___x_340_, v_fst_330_, v___x_341_, v___x_304_, v___x_341_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_450_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_450_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_450_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_450_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__3));
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v_a_305_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc_ref(v___x_356_);
v___x_357_ = l_Lean_mkConst(v___x_354_, v___x_356_);
lean_inc_ref(v_binderType_306_);
v___x_358_ = l_Lean_mkApp3(v___x_357_, v_binderType_306_, v_a_348_, v_a_350_);
if (lean_obj_tag(v_fst_334_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_432_; 
lean_del_object(v___x_352_);
v_val_359_ = lean_ctor_get(v_fst_334_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_fst_334_);
if (v_isSharedCheck_432_ == 0)
{
v___x_361_ = v_fst_334_;
v_isShared_362_ = v_isSharedCheck_432_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v_fst_334_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_432_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_mkLambdaFVars(v___x_340_, v___x_314_, v___x_341_, v___x_304_, v___x_341_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l_Lean_mkAnd(v_fst_326_, v_fst_330_);
lean_inc_ref(v___x_365_);
v___x_366_ = l_Lean_Meta_mkLambdaFVars(v___x_340_, v___x_365_, v___x_341_, v___x_304_, v___x_341_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = l_Lean_Meta_mkLambdaFVars(v___x_340_, v_val_359_, v___x_341_, v___x_304_, v___x_341_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0___closed__5));
v___x_371_ = l_Lean_mkConst(v___x_370_, v___x_356_);
v___x_372_ = l_Lean_mkApp4(v___x_371_, v_binderType_306_, v_a_364_, v_a_367_, v_a_369_);
v___x_373_ = l_Lean_Meta_mkForallFVars(v___x_340_, v___x_365_, v___x_341_, v___x_304_, v___x_304_, v___x_342_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec_ref(v___x_340_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_399_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_399_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_399_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_399_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
lean_inc(v_a_346_);
lean_inc(v_a_344_);
v___x_378_ = l_Lean_mkAnd(v_a_344_, v_a_346_);
v___x_379_ = l_Lean_Meta_mkEqTransCoreProp(v_t_307_, v_a_374_, v___x_378_, v___x_372_, v___x_358_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_379_);
v___x_381_ = v___x_361_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_398_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_box(v___x_304_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_382_);
lean_ctor_set(v___x_336_, 0, v___x_381_);
v___x_384_ = v___x_336_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_397_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_384_);
lean_ctor_set(v___x_332_, 0, v_a_346_);
v___x_386_ = v___x_332_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_346_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_396_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_386_);
lean_ctor_set(v___x_328_, 0, v_a_344_);
v___x_388_ = v___x_328_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_344_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_395_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_388_);
v___x_390_ = v___x_322_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_390_);
v___x_392_ = v___x_376_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
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
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v___x_372_);
lean_del_object(v___x_361_);
lean_dec_ref(v___x_358_);
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_322_);
lean_dec_ref(v_t_307_);
v_a_400_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_373_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_373_);
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
lean_dec(v_a_367_);
lean_dec_ref(v___x_365_);
lean_dec(v_a_364_);
lean_del_object(v___x_361_);
lean_dec_ref(v___x_358_);
lean_dec_ref_known(v___x_356_, 2);
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_322_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
v_a_408_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_368_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_368_);
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
lean_dec_ref(v___x_365_);
lean_dec(v_a_364_);
lean_del_object(v___x_361_);
lean_dec(v_val_359_);
lean_dec_ref(v___x_358_);
lean_dec_ref_known(v___x_356_, 2);
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
lean_del_object(v___x_328_);
lean_del_object(v___x_322_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
v_a_416_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_366_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_366_);
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
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_361_);
lean_dec(v_val_359_);
lean_dec_ref(v___x_358_);
lean_dec_ref_known(v___x_356_, 2);
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_322_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
v_a_424_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_363_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_363_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_object* v___x_434_; 
lean_dec_ref_known(v___x_356_, 2);
lean_dec_ref(v___x_340_);
lean_dec(v_fst_334_);
lean_dec(v_fst_330_);
lean_dec(v_fst_326_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_358_);
v___x_434_ = v___x_322_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_358_);
v___x_434_ = v_reuseFailAlloc_449_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_box(v___x_304_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_435_);
lean_ctor_set(v___x_336_, 0, v___x_434_);
v___x_437_ = v___x_336_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_448_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_437_);
lean_ctor_set(v___x_332_, 0, v_a_346_);
v___x_439_ = v___x_332_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_346_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_447_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_439_);
lean_ctor_set(v___x_328_, 0, v_a_344_);
v___x_441_ = v___x_328_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_344_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_446_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_442_);
v___x_444_ = v___x_352_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
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
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_348_);
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_dec(v_fst_334_);
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_322_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
v_a_451_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_349_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_349_);
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
lean_dec(v_a_346_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_dec(v_fst_334_);
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_322_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
v_a_459_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_347_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_347_);
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
lean_dec(v_a_344_);
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_dec(v_fst_334_);
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_322_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
v_a_467_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_345_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_345_);
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
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v___x_340_);
lean_del_object(v___x_336_);
lean_dec(v_fst_334_);
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_del_object(v___x_322_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
v_a_475_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_343_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_343_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
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
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_a_316_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_x_308_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
v___x_490_ = lean_box(0);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_490_);
v___x_492_ = v___x_318_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec_ref(v___x_314_);
lean_dec_ref(v_x_308_);
lean_dec_ref(v_t_307_);
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_305_);
return v___x_315_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_303_ = stack[0].m_obj;
uint8_t v___x_304_ = stack[1].m_num;
lean_object* v_a_305_ = stack[2].m_obj;
lean_object* v_binderType_306_ = stack[3].m_obj;
lean_object* v_t_307_ = stack[4].m_obj;
lean_object* v_x_308_ = stack[5].m_obj;
lean_object* v___y_309_ = stack[6].m_obj;
lean_object* v___y_310_ = stack[7].m_obj;
lean_object* v___y_311_ = stack[8].m_obj;
lean_object* v___y_312_ = stack[9].m_obj;
lean_object* v_res_495_;
v_res_495_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___lam__0(v_body_303_, v___x_304_, v_a_305_, v_binderType_306_, v_t_307_, v_x_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go___boxed(lean_object* v_t_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_t_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_502_;
}
}
lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object* v_e_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_isCandidate(v_e_503_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v_e_503_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Lean_Meta_Tactic_Grind_ForallAnd_0__Lean_Meta_Grind_forallImpAnd_x3f_go(v_e_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_559_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_559_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_559_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_559_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_a_516_) == 1)
{
lean_object* v_val_520_; lean_object* v_snd_521_; lean_object* v_snd_522_; lean_object* v_snd_523_; uint8_t v___x_524_; 
v_val_520_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_a_516_, 1);
v_snd_521_ = lean_ctor_get(v_val_520_, 1);
lean_inc(v_snd_521_);
v_snd_522_ = lean_ctor_get(v_snd_521_, 1);
lean_inc(v_snd_522_);
v_snd_523_ = lean_ctor_get(v_snd_522_, 1);
v___x_524_ = lean_unbox(v_snd_523_);
if (v___x_524_ == 1)
{
lean_object* v_fst_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_557_; 
v_fst_525_ = lean_ctor_get(v_snd_522_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_snd_522_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_snd_522_, 1);
lean_dec(v_unused_558_);
v___x_527_ = v_snd_522_;
v_isShared_528_ = v_isSharedCheck_557_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_fst_525_);
lean_dec(v_snd_522_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_557_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
if (lean_obj_tag(v_fst_525_) == 1)
{
lean_object* v_fst_529_; lean_object* v_fst_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_551_; 
v_fst_529_ = lean_ctor_get(v_val_520_, 0);
lean_inc(v_fst_529_);
lean_dec(v_val_520_);
v_fst_530_ = lean_ctor_get(v_snd_521_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_snd_521_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_snd_521_, 1);
lean_dec(v_unused_552_);
v___x_532_ = v_snd_521_;
v_isShared_533_ = v_isSharedCheck_551_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_fst_530_);
lean_dec(v_snd_521_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_551_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_550_; 
v_val_534_ = lean_ctor_get(v_fst_525_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_fst_525_);
if (v_isSharedCheck_550_ == 0)
{
v___x_536_ = v_fst_525_;
v_isShared_537_ = v_isSharedCheck_550_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v_fst_525_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_550_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_val_534_);
lean_ctor_set(v___x_527_, 0, v_fst_530_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_val_534_);
v___x_539_ = v_reuseFailAlloc_549_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_539_);
lean_ctor_set(v___x_532_, 0, v_fst_529_);
v___x_541_ = v___x_532_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_fst_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_548_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_541_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_543_);
v___x_545_ = v___x_518_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_555_; 
lean_del_object(v___x_527_);
lean_dec(v_fst_525_);
lean_dec(v_snd_521_);
lean_dec(v_val_520_);
v___x_553_ = lean_box(0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_553_);
v___x_555_ = v___x_518_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_dec(v_snd_522_);
lean_dec(v_snd_521_);
lean_dec(v_val_520_);
lean_del_object(v___x_518_);
goto v___jp_509_;
}
}
else
{
lean_del_object(v___x_518_);
lean_dec(v_a_516_);
goto v___jp_509_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_515_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_515_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
v___jp_509_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_forallImpAnd_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_503_ = stack[0].m_obj;
lean_object* v_a_504_ = stack[1].m_obj;
lean_object* v_a_505_ = stack[2].m_obj;
lean_object* v_a_506_ = stack[3].m_obj;
lean_object* v_a_507_ = stack[4].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f___boxed(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_575_;
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
