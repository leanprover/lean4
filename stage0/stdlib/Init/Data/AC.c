// Lean compiler output
// Module: Init.Data.AC
// Imports: public import Init.GetElem import Init.ByCases import Init.PropLemmas
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
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Data_AC_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Data_AC_instInhabitedExpr_default = (const lean_object*)&l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Data_AC_instInhabitedExpr = (const lean_object*)&l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value;
static const lean_string_object l_Lean_Data_AC_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Data.AC.Expr.var"};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Data_AC_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__1_value;
static const lean_ctor_object l_Lean_Data_AC_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__2 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__2_value;
static lean_once_cell_t l_Lean_Data_AC_instReprExpr_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__3;
static lean_once_cell_t l_Lean_Data_AC_instReprExpr_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__4;
static const lean_string_object l_Lean_Data_AC_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Data.AC.Expr.op"};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Data_AC_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__5_value)}};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Data_AC_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Data_AC_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_Data_AC_instReprExpr_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Data_AC_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instReprExpr___closed__0 = (const lean_object*)&l_Lean_Data_AC_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Data_AC_instReprExpr = (const lean_object*)&l_Lean_Data_AC_instReprExpr___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Data_AC_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Data_AC_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instBEqExpr___closed__0 = (const lean_object*)&l_Lean_Data_AC_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Data_AC_instBEqExpr = (const lean_object*)&l_Lean_Data_AC_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___closed__0 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__0_value;
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___closed__1 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__1_value;
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___closed__2 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Data_AC_instContextInformationContext___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__0_value),((lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__1_value),((lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__2_value)}};
static const lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___closed__3 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Data_AC_instContextInformationContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_AC_instContextInformationContext___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___closed__0 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__0_value;
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___closed__1 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__1_value;
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___closed__2 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__0_value),((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__1_value),((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__2_value)}};
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Data_AC_instEvalInformationContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_AC_instEvalInformationContext___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Data_AC_Expr_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_x_7_; lean_object* v___x_8_; 
v_x_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_x_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_x_7_);
return v___x_8_;
}
else
{
lean_object* v_lhs_9_; lean_object* v_rhs_10_; lean_object* v___x_11_; 
v_lhs_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_lhs_9_);
v_rhs_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_rhs_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_lhs_9_, v_rhs_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Data_AC_Expr_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim___redArg(lean_object* v_t_24_, lean_object* v_var_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_24_, v_var_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_var_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_28_, v_var_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim___redArg(lean_object* v_t_32_, lean_object* v_op_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_32_, v_op_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_op_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_36_, v_op_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Data_AC_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(2u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Data_AC_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr(lean_object* v_x_60_, lean_object* v_prec_61_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_x_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_82_; 
v_x_62_ = lean_ctor_get(v_x_60_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_82_ == 0)
{
v___x_64_ = v_x_60_;
v_isShared_65_ = v_isSharedCheck_82_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_x_62_);
lean_dec(v_x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_82_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___y_67_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_61_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__3, &l_Lean_Data_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__3);
v___y_67_ = v___x_80_;
goto v___jp_66_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__4, &l_Lean_Data_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__4);
v___y_67_ = v___x_81_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = ((lean_object*)(l_Lean_Data_AC_instReprExpr_repr___closed__2));
v___x_69_ = l_Nat_reprFast(v_x_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 3);
lean_ctor_set(v___x_64_, 0, v___x_69_);
v___x_71_ = v___x_64_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_77_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_68_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_inc(v___y_67_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___y_67_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_74_);
v___x_76_ = l_Repr_addAppParen(v___x_75_, v_prec_61_);
return v___x_76_;
}
}
}
}
else
{
lean_object* v_lhs_83_; lean_object* v_rhs_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_107_; 
v_lhs_83_ = lean_ctor_get(v_x_60_, 0);
v_rhs_84_ = lean_ctor_get(v_x_60_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_107_ == 0)
{
v___x_86_ = v_x_60_;
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_rhs_84_);
lean_inc(v_lhs_83_);
lean_dec(v_x_60_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___y_90_; uint8_t v___x_104_; 
v___x_88_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_88_, v_prec_61_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__3, &l_Lean_Data_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__3);
v___y_90_ = v___x_105_;
goto v___jp_89_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__4, &l_Lean_Data_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__4);
v___y_90_ = v___x_106_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_91_ = lean_box(1);
v___x_92_ = ((lean_object*)(l_Lean_Data_AC_instReprExpr_repr___closed__7));
v___x_93_ = l_Lean_Data_AC_instReprExpr_repr(v_lhs_83_, v___x_88_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 5);
lean_ctor_set(v___x_86_, 1, v___x_93_);
lean_ctor_set(v___x_86_, 0, v___x_92_);
v___x_95_ = v___x_86_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_103_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_91_);
v___x_97_ = l_Lean_Data_AC_instReprExpr_repr(v_rhs_84_, v___x_88_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
lean_inc(v___y_90_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_90_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
v___x_102_ = l_Repr_addAppParen(v___x_101_, v_prec_61_);
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr___boxed(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Data_AC_instReprExpr_repr(v_x_108_, v_prec_109_);
lean_dec(v_prec_109_);
return v_res_110_;
}
}
uint8_t l_Lean_Data_AC_instBEqExpr_beq(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v_x_115_; lean_object* v_x_116_; uint8_t v___x_117_; 
v_x_115_ = lean_ctor_get(v_x_113_, 0);
v_x_116_ = lean_ctor_get(v_x_114_, 0);
v___x_117_ = lean_nat_dec_eq(v_x_115_, v_x_116_);
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
else
{
if (lean_obj_tag(v_x_114_) == 1)
{
lean_object* v_lhs_119_; lean_object* v_rhs_120_; lean_object* v_lhs_121_; lean_object* v_rhs_122_; uint8_t v___x_123_; 
v_lhs_119_ = lean_ctor_get(v_x_113_, 0);
v_rhs_120_ = lean_ctor_get(v_x_113_, 1);
v_lhs_121_ = lean_ctor_get(v_x_114_, 0);
v_rhs_122_ = lean_ctor_get(v_x_114_, 1);
v___x_123_ = l_Lean_Data_AC_instBEqExpr_beq(v_lhs_119_, v_lhs_121_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
v_x_113_ = v_rhs_120_;
v_x_114_ = v_rhs_122_;
goto _start;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
}
LEAN_EXPORT void l_Lean_Data_AC_instBEqExpr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_113_ = stack[0].m_obj;
lean_object* v_x_114_ = stack[1].m_obj;
uint8_t v_res_126_;
v_res_126_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_113_, v_x_114_);
stack->m_num = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instBEqExpr_beq___boxed(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_127_, v_x_128_);
lean_dec_ref(v_x_128_);
lean_dec_ref(v_x_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg(lean_object* v_ctx_133_, lean_object* v_idx_134_){
_start:
{
lean_object* v_vars_135_; lean_object* v_arbitrary_136_; lean_object* v___x_137_; 
v_vars_135_ = lean_ctor_get(v_ctx_133_, 3);
v_arbitrary_136_ = lean_ctor_get(v_ctx_133_, 4);
v___x_137_ = l_List_get_x3fInternal___redArg(v_vars_135_, v_idx_134_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_box(0);
lean_inc(v_arbitrary_136_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_arbitrary_136_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_val_140_; 
v_val_140_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_val_140_);
lean_dec_ref_known(v___x_137_, 1);
return v_val_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg___boxed(lean_object* v_ctx_141_, lean_object* v_idx_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_141_, v_idx_142_);
lean_dec_ref(v_ctx_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var(lean_object* v_00_u03b1_144_, lean_object* v_ctx_145_, lean_object* v_idx_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_145_, v_idx_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___boxed(lean_object* v_00_u03b1_148_, lean_object* v_ctx_149_, lean_object* v_idx_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Data_AC_Context_var(v_00_u03b1_148_, v_ctx_149_, v_idx_150_);
lean_dec_ref(v_ctx_149_);
return v_res_151_;
}
}
uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(lean_object* v_ctx_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; lean_object* v_neutral_155_; 
v___x_154_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_152_, v_x_153_);
v_neutral_155_ = lean_ctor_get(v___x_154_, 1);
lean_inc(v_neutral_155_);
lean_dec_ref(v___x_154_);
if (lean_obj_tag(v_neutral_155_) == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
lean_dec_ref_known(v_neutral_155_, 1);
v___x_157_ = 1;
return v___x_157_;
}
}
}
LEAN_EXPORT void l_Lean_Data_AC_instContextInformationContext___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_152_ = stack[0].m_obj;
lean_object* v_x_153_ = stack[1].m_obj;
uint8_t v_res_158_;
v_res_158_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(v_ctx_152_, v_x_153_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(v_ctx_159_, v_x_160_);
lean_dec_ref(v_ctx_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(lean_object* v_ctx_163_){
_start:
{
lean_object* v_comm_164_; 
v_comm_164_ = lean_ctor_get(v_ctx_163_, 1);
if (lean_obj_tag(v_comm_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
uint8_t v___x_166_; 
v___x_166_ = 1;
return v___x_166_;
}
}
}
LEAN_EXPORT void l_Lean_Data_AC_instContextInformationContext___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_163_ = stack[0].m_obj;
uint8_t v_res_167_;
v_res_167_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(v_ctx_163_);
stack->m_num = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__1___boxed(lean_object* v_ctx_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(v_ctx_168_);
lean_dec_ref(v_ctx_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(lean_object* v_ctx_171_){
_start:
{
lean_object* v_idem_172_; 
v_idem_172_ = lean_ctor_get(v_ctx_171_, 2);
if (lean_obj_tag(v_idem_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 1;
return v___x_174_;
}
}
}
LEAN_EXPORT void l_Lean_Data_AC_instContextInformationContext___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_171_ = stack[0].m_obj;
uint8_t v_res_175_;
v_res_175_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(v_ctx_171_);
stack->m_num = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(v_ctx_176_);
lean_dec_ref(v_ctx_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
lean_object* l_Lean_Data_AC_instContextInformationContext___redArg(){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_Lean_Data_AC_instContextInformationContext___redArg___closed__3));
return v___x_187_;
}
}
LEAN_EXPORT void l_Lean_Data_AC_instContextInformationContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_188_;
v_res_188_ = l_Lean_Data_AC_instContextInformationContext___redArg();
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___boxed(lean_object* v___dummy_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Data_AC_instContextInformationContext___closed__0(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object* v_00_u03b1_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_Data_AC_instContextInformationContext___closed__0, &l_Lean_Data_AC_instContextInformationContext___closed__0_once, _init_l_Lean_Data_AC_instContextInformationContext___closed__0);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(lean_object* v_ctx_194_){
_start:
{
lean_object* v_arbitrary_195_; 
v_arbitrary_195_ = lean_ctor_get(v_ctx_194_, 4);
lean_inc(v_arbitrary_195_);
return v_arbitrary_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(v_ctx_196_);
lean_dec_ref(v_ctx_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__1(lean_object* v_ctx_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_op_201_; lean_object* v___x_202_; 
v_op_201_ = lean_ctor_get(v_ctx_198_, 0);
lean_inc(v_op_201_);
lean_dec_ref(v_ctx_198_);
v___x_202_ = lean_apply_2(v_op_201_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(lean_object* v_ctx_203_, lean_object* v_idx_204_){
_start:
{
lean_object* v___x_205_; lean_object* v_value_206_; 
v___x_205_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_203_, v_idx_204_);
v_value_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_value_206_);
lean_dec_ref(v___x_205_);
return v_value_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_207_, lean_object* v_idx_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(v_ctx_207_, v_idx_208_);
lean_dec_ref(v_ctx_207_);
return v_res_209_;
}
}
lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg(){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3));
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_Data_AC_instEvalInformationContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_219_;
v_res_219_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___boxed(lean_object* v___dummy_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Data_AC_instEvalInformationContext___closed__0(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext(lean_object* v_00_u03b1_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Lean_Data_AC_instEvalInformationContext___closed__0, &l_Lean_Data_AC_instEvalInformationContext___closed__0_once, _init_l_Lean_Data_AC_instEvalInformationContext___closed__0);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval___redArg(lean_object* v_inst_225_, lean_object* v_ctx_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v_x_228_; lean_object* v_evalVar_229_; lean_object* v___x_230_; 
v_x_228_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_x_228_);
lean_dec_ref_known(v_x_227_, 1);
v_evalVar_229_ = lean_ctor_get(v_inst_225_, 2);
lean_inc(v_evalVar_229_);
lean_dec_ref(v_inst_225_);
v___x_230_ = lean_apply_2(v_evalVar_229_, v_ctx_226_, v_x_228_);
return v___x_230_;
}
else
{
lean_object* v_lhs_231_; lean_object* v_rhs_232_; lean_object* v_evalOp_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_lhs_231_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_lhs_231_);
v_rhs_232_ = lean_ctor_get(v_x_227_, 1);
lean_inc_ref(v_rhs_232_);
lean_dec_ref_known(v_x_227_, 2);
v_evalOp_233_ = lean_ctor_get(v_inst_225_, 1);
lean_inc(v_evalOp_233_);
lean_inc_n(v_ctx_226_, 2);
lean_inc_ref(v_inst_225_);
v___x_234_ = l_Lean_Data_AC_eval___redArg(v_inst_225_, v_ctx_226_, v_lhs_231_);
v___x_235_ = l_Lean_Data_AC_eval___redArg(v_inst_225_, v_ctx_226_, v_rhs_232_);
v___x_236_ = lean_apply_3(v_evalOp_233_, v_ctx_226_, v___x_234_, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_ctx_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Data_AC_eval___redArg(v_inst_239_, v_ctx_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList(lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v_x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_x_244_ = lean_ctor_get(v_x_243_, 0);
v___x_245_ = lean_box(0);
lean_inc(v_x_244_);
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v_lhs_247_; lean_object* v_rhs_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_lhs_247_ = lean_ctor_get(v_x_243_, 0);
v_rhs_248_ = lean_ctor_get(v_x_243_, 1);
v___x_249_ = l_Lean_Data_AC_Expr_toList(v_lhs_247_);
v___x_250_ = l_Lean_Data_AC_Expr_toList(v_rhs_248_);
v___x_251_ = l_List_appendTR___redArg(v___x_249_, v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Data_AC_Expr_toList(v_x_252_);
lean_dec_ref(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___redArg(lean_object* v_inst_254_, lean_object* v_ctx_255_, lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_arbitrary_257_; lean_object* v___x_258_; 
v_arbitrary_257_ = lean_ctor_get(v_inst_254_, 0);
lean_inc(v_arbitrary_257_);
lean_dec_ref(v_inst_254_);
v___x_258_ = lean_apply_1(v_arbitrary_257_, v_ctx_255_);
return v___x_258_;
}
else
{
lean_object* v_tail_259_; 
v_tail_259_ = lean_ctor_get(v_x_256_, 1);
if (lean_obj_tag(v_tail_259_) == 0)
{
lean_object* v_head_260_; lean_object* v_evalVar_261_; lean_object* v___x_262_; 
v_head_260_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_head_260_);
lean_dec_ref_known(v_x_256_, 2);
v_evalVar_261_ = lean_ctor_get(v_inst_254_, 2);
lean_inc(v_evalVar_261_);
lean_dec_ref(v_inst_254_);
v___x_262_ = lean_apply_2(v_evalVar_261_, v_ctx_255_, v_head_260_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v_evalOp_264_; lean_object* v_evalVar_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_inc(v_tail_259_);
v_head_263_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_head_263_);
lean_dec_ref_known(v_x_256_, 2);
v_evalOp_264_ = lean_ctor_get(v_inst_254_, 1);
lean_inc(v_evalOp_264_);
v_evalVar_265_ = lean_ctor_get(v_inst_254_, 2);
lean_inc(v_evalVar_265_);
lean_inc_n(v_ctx_255_, 2);
v___x_266_ = lean_apply_2(v_evalVar_265_, v_ctx_255_, v_head_263_);
v___x_267_ = l_Lean_Data_AC_evalList___redArg(v_inst_254_, v_ctx_255_, v_tail_259_);
v___x_268_ = lean_apply_3(v_evalOp_264_, v_ctx_255_, v___x_266_, v___x_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_ctx_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Data_AC_evalList___redArg(v_inst_271_, v_ctx_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_insert(lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v_x_275_);
lean_ctor_set(v___x_277_, 1, v_x_276_);
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; uint8_t v___x_280_; 
v_head_278_ = lean_ctor_get(v_x_276_, 0);
v_tail_279_ = lean_ctor_get(v_x_276_, 1);
v___x_280_ = lean_nat_dec_lt(v_x_275_, v_head_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
lean_inc(v_tail_279_);
lean_inc(v_head_278_);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; 
v_unused_289_ = lean_ctor_get(v_x_276_, 1);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_x_276_, 0);
lean_dec(v_unused_290_);
v___x_282_ = v_x_276_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_Data_AC_insert(v_x_275_, v_tail_279_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_head_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v_x_275_);
lean_ctor_set(v___x_291_, 1, v_x_276_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort_loop(lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
if (lean_obj_tag(v_a_293_) == 0)
{
return v_a_292_;
}
else
{
lean_object* v_head_294_; lean_object* v_tail_295_; lean_object* v___x_296_; 
v_head_294_ = lean_ctor_get(v_a_293_, 0);
lean_inc(v_head_294_);
v_tail_295_ = lean_ctor_get(v_a_293_, 1);
lean_inc(v_tail_295_);
lean_dec_ref_known(v_a_293_, 2);
v___x_296_ = l_Lean_Data_AC_insert(v_head_294_, v_a_292_);
v_a_292_ = v___x_296_;
v_a_293_ = v_tail_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort(lean_object* v_xs_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = l_Lean_Data_AC_sort_loop(v___x_299_, v_xs_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem_loop(lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
if (lean_obj_tag(v_a_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v_a_301_);
lean_ctor_set(v___x_303_, 1, v_a_302_);
return v___x_303_;
}
else
{
lean_object* v_head_304_; lean_object* v_tail_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v_head_304_ = lean_ctor_get(v_a_302_, 0);
v_tail_305_ = lean_ctor_get(v_a_302_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_a_302_);
if (v_isSharedCheck_315_ == 0)
{
v___x_307_ = v_a_302_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_tail_305_);
lean_inc(v_head_304_);
lean_dec(v_a_302_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; 
v___x_309_ = lean_nat_dec_eq(v_a_301_, v_head_304_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Data_AC_mergeIdem_loop(v_head_304_, v_tail_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_310_);
lean_ctor_set(v___x_307_, 0, v_a_301_);
v___x_312_ = v___x_307_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_del_object(v___x_307_);
lean_dec(v_head_304_);
v_a_302_ = v_tail_305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem(lean_object* v_xs_316_){
_start:
{
if (lean_obj_tag(v_xs_316_) == 0)
{
return v_xs_316_;
}
else
{
lean_object* v_head_317_; lean_object* v_tail_318_; lean_object* v___x_319_; 
v_head_317_ = lean_ctor_get(v_xs_316_, 0);
lean_inc(v_head_317_);
v_tail_318_ = lean_ctor_get(v_xs_316_, 1);
lean_inc(v_tail_318_);
lean_dec_ref_known(v_xs_316_, 2);
v___x_319_ = l_Lean_Data_AC_mergeIdem_loop(v_head_317_, v_tail_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___redArg(lean_object* v_info_320_, lean_object* v_ctx_321_, lean_object* v_a_322_){
_start:
{
if (lean_obj_tag(v_a_322_) == 0)
{
lean_dec(v_ctx_321_);
lean_dec_ref(v_info_320_);
return v_a_322_;
}
else
{
lean_object* v_head_323_; lean_object* v_tail_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_336_; 
v_head_323_ = lean_ctor_get(v_a_322_, 0);
v_tail_324_ = lean_ctor_get(v_a_322_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_a_322_);
if (v_isSharedCheck_336_ == 0)
{
v___x_326_ = v_a_322_;
v_isShared_327_ = v_isSharedCheck_336_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_tail_324_);
lean_inc(v_head_323_);
lean_dec(v_a_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_336_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_isNeutral_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_isNeutral_328_ = lean_ctor_get(v_info_320_, 0);
lean_inc_ref(v_isNeutral_328_);
lean_inc(v_head_323_);
lean_inc(v_ctx_321_);
v___x_329_ = lean_apply_2(v_isNeutral_328_, v_ctx_321_, v_head_323_);
v___x_330_ = lean_unbox(v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_320_, v_ctx_321_, v_tail_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_331_);
v___x_333_ = v___x_326_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_head_323_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_del_object(v___x_326_);
lean_dec(v_head_323_);
v_a_322_ = v_tail_324_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop(lean_object* v_00_u03b1_337_, lean_object* v_info_338_, lean_object* v_ctx_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_338_, v_ctx_339_, v_a_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___redArg(lean_object* v_info_342_, lean_object* v_ctx_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
lean_dec(v_ctx_343_);
lean_dec_ref(v_info_342_);
return v_x_344_;
}
else
{
lean_object* v_head_345_; lean_object* v___x_346_; 
v_head_345_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_head_345_);
v___x_346_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_342_, v_ctx_343_, v_x_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v_head_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
else
{
lean_dec(v_head_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals(lean_object* v_00_u03b1_348_, lean_object* v_info_349_, lean_object* v_ctx_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_349_, v_ctx_350_, v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg(lean_object* v_info_353_, lean_object* v_ctx_354_, lean_object* v_e_355_){
_start:
{
lean_object* v_isComm_356_; lean_object* v_isIdem_357_; lean_object* v___y_359_; lean_object* v_xs_363_; lean_object* v_xs_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_isComm_356_ = lean_ctor_get(v_info_353_, 1);
lean_inc_ref(v_isComm_356_);
v_isIdem_357_ = lean_ctor_get(v_info_353_, 2);
lean_inc_ref(v_isIdem_357_);
v_xs_363_ = l_Lean_Data_AC_Expr_toList(v_e_355_);
lean_inc_n(v_ctx_354_, 2);
v_xs_364_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_353_, v_ctx_354_, v_xs_363_);
v___x_365_ = lean_apply_1(v_isComm_356_, v_ctx_354_);
v___x_366_ = lean_unbox(v___x_365_);
if (v___x_366_ == 0)
{
v___y_359_ = v_xs_364_;
goto v___jp_358_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Data_AC_sort(v_xs_364_);
v___y_359_ = v___x_367_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_apply_1(v_isIdem_357_, v_ctx_354_);
v___x_361_ = lean_unbox(v___x_360_);
if (v___x_361_ == 0)
{
return v___y_359_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Data_AC_mergeIdem(v___y_359_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg___boxed(lean_object* v_info_368_, lean_object* v_ctx_369_, lean_object* v_e_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Data_AC_norm___redArg(v_info_368_, v_ctx_369_, v_e_370_);
lean_dec_ref(v_e_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm(lean_object* v_00_u03b1_372_, lean_object* v_info_373_, lean_object* v_ctx_374_, lean_object* v_e_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Data_AC_norm___redArg(v_info_373_, v_ctx_374_, v_e_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___boxed(lean_object* v_00_u03b1_377_, lean_object* v_info_378_, lean_object* v_ctx_379_, lean_object* v_e_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Data_AC_norm(v_00_u03b1_377_, v_info_378_, v_ctx_379_, v_e_380_);
lean_dec_ref(v_e_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_apply_1(v_h__2_384_, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
lean_dec(v_h__2_384_);
v_val_387_ = lean_ctor_get(v_x_382_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_x_382_, 1);
v___x_388_ = lean_apply_1(v_h__1_383_, v_val_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_389_, lean_object* v_motive_390_, lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_h__1_392_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_apply_1(v_h__2_393_, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; 
lean_dec(v_h__2_393_);
v_val_396_ = lean_ctor_get(v_x_391_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v_x_391_, 1);
v___x_397_ = lean_apply_1(v_h__1_392_, v_val_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object* v_x_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_, lean_object* v_h__3_401_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_h__3_401_);
lean_dec(v_h__2_400_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_apply_1(v_h__1_399_, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v_tail_404_; 
lean_dec(v_h__1_399_);
v_tail_404_ = lean_ctor_get(v_x_398_, 1);
if (lean_obj_tag(v_tail_404_) == 0)
{
lean_object* v_head_405_; lean_object* v___x_406_; 
lean_dec(v_h__3_401_);
v_head_405_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_head_405_);
lean_dec_ref_known(v_x_398_, 2);
v___x_406_ = lean_apply_1(v_h__2_400_, v_head_405_);
return v___x_406_;
}
else
{
lean_object* v_head_407_; lean_object* v___x_408_; 
lean_inc(v_tail_404_);
lean_dec(v_h__2_400_);
v_head_407_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_head_407_);
lean_dec_ref_known(v_x_398_, 2);
v___x_408_ = lean_apply_3(v_h__3_401_, v_head_407_, v_tail_404_, lean_box(0));
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_, lean_object* v_h__3_413_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_h__3_413_);
lean_dec(v_h__2_412_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_apply_1(v_h__1_411_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_tail_416_; 
lean_dec(v_h__1_411_);
v_tail_416_ = lean_ctor_get(v_x_410_, 1);
if (lean_obj_tag(v_tail_416_) == 0)
{
lean_object* v_head_417_; lean_object* v___x_418_; 
lean_dec(v_h__3_413_);
v_head_417_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_head_417_);
lean_dec_ref_known(v_x_410_, 2);
v___x_418_ = lean_apply_1(v_h__2_412_, v_head_417_);
return v___x_418_;
}
else
{
lean_object* v_head_419_; lean_object* v___x_420_; 
lean_inc(v_tail_416_);
lean_dec(v_h__2_412_);
v_head_419_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_head_419_);
lean_dec_ref_known(v_x_410_, 2);
v___x_420_ = lean_apply_3(v_h__3_413_, v_head_419_, v_tail_416_, lean_box(0));
return v___x_420_;
}
}
}
}
lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(uint8_t v_x_421_, lean_object* v_h__1_422_, lean_object* v_h__2_423_){
_start:
{
if (v_x_421_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_422_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_apply_1(v_h__2_423_, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_423_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_apply_1(v_h__1_422_, v___x_426_);
return v___x_427_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_421_ = stack[0].m_num;
lean_object* v_h__1_422_ = stack[1].m_obj;
lean_object* v_h__2_423_ = stack[2].m_obj;
lean_object* v_res_428_;
v_res_428_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(v_x_421_, v_h__1_422_, v_h__2_423_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_){
_start:
{
uint8_t v_x_24__boxed_432_; lean_object* v_res_433_; 
v_x_24__boxed_432_ = lean_unbox(v_x_429_);
v_res_433_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(v_x_24__boxed_432_, v_h__1_430_, v_h__2_431_);
return v_res_433_;
}
}
lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_object* v_motive_434_, uint8_t v_x_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_){
_start:
{
if (v_x_435_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_436_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_apply_1(v_h__2_437_, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_h__2_437_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_1(v_h__1_436_, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_435_ = stack[1].m_num;
lean_object* v_h__1_436_ = stack[2].m_obj;
lean_object* v_h__2_437_ = stack[3].m_obj;
lean_object* v_res_442_;
v_res_442_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_box(0), v_x_435_, v_h__1_436_, v_h__2_437_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(lean_object* v_motive_443_, lean_object* v_x_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_){
_start:
{
uint8_t v_x_41__boxed_447_; lean_object* v_res_448_; 
v_x_41__boxed_447_ = lean_unbox(v_x_444_);
v_res_448_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(v_motive_443_, v_x_41__boxed_447_, v_h__1_445_, v_h__2_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(lean_object* v_x_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_451_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_apply_1(v_h__1_450_, v___x_452_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
lean_dec(v_h__1_450_);
v___x_454_ = lean_apply_2(v_h__2_451_, v_x_449_, lean_box(0));
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(lean_object* v_motive_455_, lean_object* v_x_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_h__2_458_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_apply_1(v_h__1_457_, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_h__1_457_);
v___x_461_ = lean_apply_2(v_h__2_458_, v_x_456_, lean_box(0));
return v___x_461_;
}
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_AC(builtin);
}
#ifdef __cplusplus
}
#endif
