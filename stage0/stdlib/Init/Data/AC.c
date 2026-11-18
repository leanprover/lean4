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
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Data_AC_instBEqExpr_beq(lean_object* v_x_113_, lean_object* v_x_114_){
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
LEAN_EXPORT lean_object* l_Lean_Data_AC_instBEqExpr_beq___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_126_, v_x_127_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg(lean_object* v_ctx_132_, lean_object* v_idx_133_){
_start:
{
lean_object* v_vars_134_; lean_object* v_arbitrary_135_; lean_object* v___x_136_; 
v_vars_134_ = lean_ctor_get(v_ctx_132_, 3);
v_arbitrary_135_ = lean_ctor_get(v_ctx_132_, 4);
v___x_136_ = l_List_get_x3fInternal___redArg(v_vars_134_, v_idx_133_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_box(0);
lean_inc(v_arbitrary_135_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_arbitrary_135_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_val_139_; 
v_val_139_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v___x_136_, 1);
return v_val_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___redArg___boxed(lean_object* v_ctx_140_, lean_object* v_idx_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_140_, v_idx_141_);
lean_dec_ref(v_ctx_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var(lean_object* v_00_u03b1_143_, lean_object* v_ctx_144_, lean_object* v_idx_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_144_, v_idx_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Context_var___boxed(lean_object* v_00_u03b1_147_, lean_object* v_ctx_148_, lean_object* v_idx_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Data_AC_Context_var(v_00_u03b1_147_, v_ctx_148_, v_idx_149_);
lean_dec_ref(v_ctx_148_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(lean_object* v_ctx_151_, lean_object* v_x_152_){
_start:
{
lean_object* v___x_153_; lean_object* v_neutral_154_; 
v___x_153_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_151_, v_x_152_);
v_neutral_154_ = lean_ctor_get(v___x_153_, 1);
lean_inc(v_neutral_154_);
lean_dec_ref(v___x_153_);
if (lean_obj_tag(v_neutral_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
lean_dec_ref_known(v_neutral_154_, 1);
v___x_156_ = 1;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(v_ctx_157_, v_x_158_);
lean_dec_ref(v_ctx_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(lean_object* v_ctx_161_){
_start:
{
lean_object* v_comm_162_; 
v_comm_162_ = lean_ctor_get(v_ctx_161_, 1);
if (lean_obj_tag(v_comm_162_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__1___boxed(lean_object* v_ctx_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(v_ctx_165_);
lean_dec_ref(v_ctx_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(lean_object* v_ctx_168_){
_start:
{
lean_object* v_idem_169_; 
v_idem_169_ = lean_ctor_get(v_ctx_168_, 2);
if (lean_obj_tag(v_idem_169_) == 0)
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 1;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(v_ctx_172_);
lean_dec_ref(v_ctx_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg(){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_Lean_Data_AC_instContextInformationContext___redArg___closed__3));
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___boxed(lean_object* v___dummy_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v_res_185_;
}
}
static lean_object* _init_l_Lean_Data_AC_instContextInformationContext___closed__0(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object* v_00_u03b1_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_Data_AC_instContextInformationContext___closed__0, &l_Lean_Data_AC_instContextInformationContext___closed__0_once, _init_l_Lean_Data_AC_instContextInformationContext___closed__0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(lean_object* v_ctx_189_){
_start:
{
lean_object* v_arbitrary_190_; 
v_arbitrary_190_ = lean_ctor_get(v_ctx_189_, 4);
lean_inc(v_arbitrary_190_);
return v_arbitrary_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(v_ctx_191_);
lean_dec_ref(v_ctx_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__1(lean_object* v_ctx_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_op_196_; lean_object* v___x_197_; 
v_op_196_ = lean_ctor_get(v_ctx_193_, 0);
lean_inc(v_op_196_);
lean_dec_ref(v_ctx_193_);
v___x_197_ = lean_apply_2(v_op_196_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(lean_object* v_ctx_198_, lean_object* v_idx_199_){
_start:
{
lean_object* v___x_200_; lean_object* v_value_201_; 
v___x_200_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_198_, v_idx_199_);
v_value_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_value_201_);
lean_dec_ref(v___x_200_);
return v_value_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_202_, lean_object* v_idx_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(v_ctx_202_, v_idx_203_);
lean_dec_ref(v_ctx_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg(){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3));
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___boxed(lean_object* v___dummy_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v_res_215_;
}
}
static lean_object* _init_l_Lean_Data_AC_instEvalInformationContext___closed__0(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext(lean_object* v_00_u03b1_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Data_AC_instEvalInformationContext___closed__0, &l_Lean_Data_AC_instEvalInformationContext___closed__0_once, _init_l_Lean_Data_AC_instEvalInformationContext___closed__0);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval___redArg(lean_object* v_inst_219_, lean_object* v_ctx_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v_x_222_; lean_object* v_evalVar_223_; lean_object* v___x_224_; 
v_x_222_ = lean_ctor_get(v_x_221_, 0);
lean_inc(v_x_222_);
lean_dec_ref_known(v_x_221_, 1);
v_evalVar_223_ = lean_ctor_get(v_inst_219_, 2);
lean_inc(v_evalVar_223_);
lean_dec_ref(v_inst_219_);
v___x_224_ = lean_apply_2(v_evalVar_223_, v_ctx_220_, v_x_222_);
return v___x_224_;
}
else
{
lean_object* v_lhs_225_; lean_object* v_rhs_226_; lean_object* v_evalOp_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_lhs_225_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_lhs_225_);
v_rhs_226_ = lean_ctor_get(v_x_221_, 1);
lean_inc_ref(v_rhs_226_);
lean_dec_ref_known(v_x_221_, 2);
v_evalOp_227_ = lean_ctor_get(v_inst_219_, 1);
lean_inc(v_evalOp_227_);
lean_inc_n(v_ctx_220_, 2);
lean_inc_ref(v_inst_219_);
v___x_228_ = l_Lean_Data_AC_eval___redArg(v_inst_219_, v_ctx_220_, v_lhs_225_);
v___x_229_ = l_Lean_Data_AC_eval___redArg(v_inst_219_, v_ctx_220_, v_rhs_226_);
v___x_230_ = lean_apply_3(v_evalOp_227_, v_ctx_220_, v___x_228_, v___x_229_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_inst_233_, lean_object* v_ctx_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Data_AC_eval___redArg(v_inst_233_, v_ctx_234_, v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_x_238_ = lean_ctor_get(v_x_237_, 0);
v___x_239_ = lean_box(0);
lean_inc(v_x_238_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_lhs_241_; lean_object* v_rhs_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_lhs_241_ = lean_ctor_get(v_x_237_, 0);
v_rhs_242_ = lean_ctor_get(v_x_237_, 1);
v___x_243_ = l_Lean_Data_AC_Expr_toList(v_lhs_241_);
v___x_244_ = l_Lean_Data_AC_Expr_toList(v_rhs_242_);
v___x_245_ = l_List_appendTR___redArg(v___x_243_, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList___boxed(lean_object* v_x_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Data_AC_Expr_toList(v_x_246_);
lean_dec_ref(v_x_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___redArg(lean_object* v_inst_248_, lean_object* v_ctx_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v_arbitrary_251_; lean_object* v___x_252_; 
v_arbitrary_251_ = lean_ctor_get(v_inst_248_, 0);
lean_inc(v_arbitrary_251_);
lean_dec_ref(v_inst_248_);
v___x_252_ = lean_apply_1(v_arbitrary_251_, v_ctx_249_);
return v___x_252_;
}
else
{
lean_object* v_tail_253_; 
v_tail_253_ = lean_ctor_get(v_x_250_, 1);
if (lean_obj_tag(v_tail_253_) == 0)
{
lean_object* v_head_254_; lean_object* v_evalVar_255_; lean_object* v___x_256_; 
v_head_254_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_head_254_);
lean_dec_ref_known(v_x_250_, 2);
v_evalVar_255_ = lean_ctor_get(v_inst_248_, 2);
lean_inc(v_evalVar_255_);
lean_dec_ref(v_inst_248_);
v___x_256_ = lean_apply_2(v_evalVar_255_, v_ctx_249_, v_head_254_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_evalOp_258_; lean_object* v_evalVar_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
lean_inc(v_tail_253_);
v_head_257_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_head_257_);
lean_dec_ref_known(v_x_250_, 2);
v_evalOp_258_ = lean_ctor_get(v_inst_248_, 1);
lean_inc(v_evalOp_258_);
v_evalVar_259_ = lean_ctor_get(v_inst_248_, 2);
lean_inc(v_evalVar_259_);
lean_inc_n(v_ctx_249_, 2);
v___x_260_ = lean_apply_2(v_evalVar_259_, v_ctx_249_, v_head_257_);
v___x_261_ = l_Lean_Data_AC_evalList___redArg(v_inst_248_, v_ctx_249_, v_tail_253_);
v___x_262_ = lean_apply_3(v_evalOp_258_, v_ctx_249_, v___x_260_, v___x_261_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_inst_265_, lean_object* v_ctx_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Data_AC_evalList___redArg(v_inst_265_, v_ctx_266_, v_x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_insert(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v_x_269_);
lean_ctor_set(v___x_271_, 1, v_x_270_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; uint8_t v___x_274_; 
v_head_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 1);
v___x_274_ = lean_nat_dec_lt(v_x_269_, v_head_272_);
if (v___x_274_ == 0)
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
lean_inc(v_tail_273_);
lean_inc(v_head_272_);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; lean_object* v_unused_284_; 
v_unused_283_ = lean_ctor_get(v_x_270_, 1);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_x_270_, 0);
lean_dec(v_unused_284_);
v___x_276_ = v_x_270_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_x_270_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = l_Lean_Data_AC_insert(v_x_269_, v_tail_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_head_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v_x_269_);
lean_ctor_set(v___x_285_, 1, v_x_270_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort_loop(lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
if (lean_obj_tag(v_a_287_) == 0)
{
return v_a_286_;
}
else
{
lean_object* v_head_288_; lean_object* v_tail_289_; lean_object* v___x_290_; 
v_head_288_ = lean_ctor_get(v_a_287_, 0);
lean_inc(v_head_288_);
v_tail_289_ = lean_ctor_get(v_a_287_, 1);
lean_inc(v_tail_289_);
lean_dec_ref_known(v_a_287_, 2);
v___x_290_ = l_Lean_Data_AC_insert(v_head_288_, v_a_286_);
v_a_286_ = v___x_290_;
v_a_287_ = v_tail_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort(lean_object* v_xs_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(0);
v___x_294_ = l_Lean_Data_AC_sort_loop(v___x_293_, v_xs_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem_loop(lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
if (lean_obj_tag(v_a_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v_a_295_);
lean_ctor_set(v___x_297_, 1, v_a_296_);
return v___x_297_;
}
else
{
lean_object* v_head_298_; lean_object* v_tail_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v_head_298_ = lean_ctor_get(v_a_296_, 0);
v_tail_299_ = lean_ctor_get(v_a_296_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_309_ == 0)
{
v___x_301_ = v_a_296_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_tail_299_);
lean_inc(v_head_298_);
lean_dec(v_a_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_a_295_, v_head_298_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_Data_AC_mergeIdem_loop(v_head_298_, v_tail_299_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_304_);
lean_ctor_set(v___x_301_, 0, v_a_295_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_295_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_del_object(v___x_301_);
lean_dec(v_head_298_);
v_a_296_ = v_tail_299_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem(lean_object* v_xs_310_){
_start:
{
if (lean_obj_tag(v_xs_310_) == 0)
{
return v_xs_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v___x_313_; 
v_head_311_ = lean_ctor_get(v_xs_310_, 0);
lean_inc(v_head_311_);
v_tail_312_ = lean_ctor_get(v_xs_310_, 1);
lean_inc(v_tail_312_);
lean_dec_ref_known(v_xs_310_, 2);
v___x_313_ = l_Lean_Data_AC_mergeIdem_loop(v_head_311_, v_tail_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___redArg(lean_object* v_info_314_, lean_object* v_ctx_315_, lean_object* v_a_316_){
_start:
{
if (lean_obj_tag(v_a_316_) == 0)
{
lean_dec(v_ctx_315_);
lean_dec_ref(v_info_314_);
return v_a_316_;
}
else
{
lean_object* v_head_317_; lean_object* v_tail_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_330_; 
v_head_317_ = lean_ctor_get(v_a_316_, 0);
v_tail_318_ = lean_ctor_get(v_a_316_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_330_ == 0)
{
v___x_320_ = v_a_316_;
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tail_318_);
lean_inc(v_head_317_);
lean_dec(v_a_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_isNeutral_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_isNeutral_322_ = lean_ctor_get(v_info_314_, 0);
lean_inc_ref(v_isNeutral_322_);
lean_inc(v_head_317_);
lean_inc(v_ctx_315_);
v___x_323_ = lean_apply_2(v_isNeutral_322_, v_ctx_315_, v_head_317_);
v___x_324_ = lean_unbox(v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_314_, v_ctx_315_, v_tail_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_325_);
v___x_327_ = v___x_320_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_head_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
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
lean_del_object(v___x_320_);
lean_dec(v_head_317_);
v_a_316_ = v_tail_318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop(lean_object* v_00_u03b1_331_, lean_object* v_info_332_, lean_object* v_ctx_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_332_, v_ctx_333_, v_a_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___redArg(lean_object* v_info_336_, lean_object* v_ctx_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_dec(v_ctx_337_);
lean_dec_ref(v_info_336_);
return v_x_338_;
}
else
{
lean_object* v_head_339_; lean_object* v___x_340_; 
v_head_339_ = lean_ctor_get(v_x_338_, 0);
lean_inc(v_head_339_);
v___x_340_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_336_, v_ctx_337_, v_x_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_head_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
return v___x_341_;
}
else
{
lean_dec(v_head_339_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals(lean_object* v_00_u03b1_342_, lean_object* v_info_343_, lean_object* v_ctx_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_343_, v_ctx_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg(lean_object* v_info_347_, lean_object* v_ctx_348_, lean_object* v_e_349_){
_start:
{
lean_object* v_isComm_350_; lean_object* v_isIdem_351_; lean_object* v___y_353_; lean_object* v_xs_357_; lean_object* v_xs_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_isComm_350_ = lean_ctor_get(v_info_347_, 1);
lean_inc_ref(v_isComm_350_);
v_isIdem_351_ = lean_ctor_get(v_info_347_, 2);
lean_inc_ref(v_isIdem_351_);
v_xs_357_ = l_Lean_Data_AC_Expr_toList(v_e_349_);
lean_inc_n(v_ctx_348_, 2);
v_xs_358_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_347_, v_ctx_348_, v_xs_357_);
v___x_359_ = lean_apply_1(v_isComm_350_, v_ctx_348_);
v___x_360_ = lean_unbox(v___x_359_);
if (v___x_360_ == 0)
{
v___y_353_ = v_xs_358_;
goto v___jp_352_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Data_AC_sort(v_xs_358_);
v___y_353_ = v___x_361_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_apply_1(v_isIdem_351_, v_ctx_348_);
v___x_355_ = lean_unbox(v___x_354_);
if (v___x_355_ == 0)
{
return v___y_353_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Data_AC_mergeIdem(v___y_353_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg___boxed(lean_object* v_info_362_, lean_object* v_ctx_363_, lean_object* v_e_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Data_AC_norm___redArg(v_info_362_, v_ctx_363_, v_e_364_);
lean_dec_ref(v_e_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm(lean_object* v_00_u03b1_366_, lean_object* v_info_367_, lean_object* v_ctx_368_, lean_object* v_e_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Data_AC_norm___redArg(v_info_367_, v_ctx_368_, v_e_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___boxed(lean_object* v_00_u03b1_371_, lean_object* v_info_372_, lean_object* v_ctx_373_, lean_object* v_e_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Data_AC_norm(v_00_u03b1_371_, v_info_372_, v_ctx_373_, v_e_374_);
lean_dec_ref(v_e_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(lean_object* v_x_376_, lean_object* v_h__1_377_, lean_object* v_h__2_378_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__2_378_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__1_377_, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v_head_381_; lean_object* v_tail_382_; lean_object* v___x_383_; 
lean_dec(v_h__1_377_);
v_head_381_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_head_381_);
v_tail_382_ = lean_ctor_get(v_x_376_, 1);
lean_inc(v_tail_382_);
lean_dec_ref_known(v_x_376_, 2);
v___x_383_ = lean_apply_2(v_h__2_378_, v_head_381_, v_tail_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(lean_object* v_motive_384_, lean_object* v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_h__2_387_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_apply_1(v_h__1_386_, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v_head_390_; lean_object* v_tail_391_; lean_object* v___x_392_; 
lean_dec(v_h__1_386_);
v_head_390_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_head_390_);
v_tail_391_ = lean_ctor_get(v_x_385_, 1);
lean_inc(v_tail_391_);
lean_dec_ref_known(v_x_385_, 2);
v___x_392_ = lean_apply_2(v_h__2_387_, v_head_390_, v_tail_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_397_; 
lean_dec(v_h__1_395_);
v___x_397_ = lean_apply_1(v_h__2_396_, v_x_393_);
return v___x_397_;
}
else
{
lean_object* v_head_398_; lean_object* v_tail_399_; lean_object* v___x_400_; 
lean_dec(v_h__2_396_);
v_head_398_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_head_398_);
v_tail_399_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_tail_399_);
lean_dec_ref_known(v_x_394_, 2);
v___x_400_ = lean_apply_3(v_h__1_395_, v_x_393_, v_head_398_, v_tail_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(lean_object* v_motive_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_h__1_404_, lean_object* v_h__2_405_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v___x_406_; 
lean_dec(v_h__1_404_);
v___x_406_ = lean_apply_1(v_h__2_405_, v_x_402_);
return v___x_406_;
}
else
{
lean_object* v_head_407_; lean_object* v_tail_408_; lean_object* v___x_409_; 
lean_dec(v_h__2_405_);
v_head_407_ = lean_ctor_get(v_x_403_, 0);
lean_inc(v_head_407_);
v_tail_408_ = lean_ctor_get(v_x_403_, 1);
lean_inc(v_tail_408_);
lean_dec_ref_known(v_x_403_, 2);
v___x_409_ = lean_apply_3(v_h__1_404_, v_x_402_, v_head_407_, v_tail_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_h__1_411_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_1(v_h__2_412_, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; 
lean_dec(v_h__2_412_);
v_val_415_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_x_410_, 1);
v___x_416_ = lean_apply_1(v_h__1_411_, v_val_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_417_, lean_object* v_motive_418_, lean_object* v_x_419_, lean_object* v_h__1_420_, lean_object* v_h__2_421_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_420_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_apply_1(v_h__2_421_, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_425_; 
lean_dec(v_h__2_421_);
v_val_424_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v_x_419_, 1);
v___x_425_ = lean_apply_1(v_h__1_420_, v_val_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_h__3_429_);
lean_dec(v_h__2_428_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_apply_1(v_h__1_427_, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_tail_432_; 
lean_dec(v_h__1_427_);
v_tail_432_ = lean_ctor_get(v_x_426_, 1);
if (lean_obj_tag(v_tail_432_) == 0)
{
lean_object* v_head_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_429_);
v_head_433_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_head_433_);
lean_dec_ref_known(v_x_426_, 2);
v___x_434_ = lean_apply_1(v_h__2_428_, v_head_433_);
return v___x_434_;
}
else
{
lean_object* v_head_435_; lean_object* v___x_436_; 
lean_inc(v_tail_432_);
lean_dec(v_h__2_428_);
v_head_435_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_head_435_);
lean_dec_ref_known(v_x_426_, 2);
v___x_436_ = lean_apply_3(v_h__3_429_, v_head_435_, v_tail_432_, lean_box(0));
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object* v_motive_437_, lean_object* v_x_438_, lean_object* v_h__1_439_, lean_object* v_h__2_440_, lean_object* v_h__3_441_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_h__3_441_);
lean_dec(v_h__2_440_);
v___x_442_ = lean_box(0);
v___x_443_ = lean_apply_1(v_h__1_439_, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v_tail_444_; 
lean_dec(v_h__1_439_);
v_tail_444_ = lean_ctor_get(v_x_438_, 1);
if (lean_obj_tag(v_tail_444_) == 0)
{
lean_object* v_head_445_; lean_object* v___x_446_; 
lean_dec(v_h__3_441_);
v_head_445_ = lean_ctor_get(v_x_438_, 0);
lean_inc(v_head_445_);
lean_dec_ref_known(v_x_438_, 2);
v___x_446_ = lean_apply_1(v_h__2_440_, v_head_445_);
return v___x_446_;
}
else
{
lean_object* v_head_447_; lean_object* v___x_448_; 
lean_inc(v_tail_444_);
lean_dec(v_h__2_440_);
v_head_447_ = lean_ctor_get(v_x_438_, 0);
lean_inc(v_head_447_);
lean_dec_ref_known(v_x_438_, 2);
v___x_448_ = lean_apply_3(v_h__3_441_, v_head_447_, v_tail_444_, lean_box(0));
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_453_; 
lean_dec(v_h__2_452_);
v___x_453_ = lean_apply_1(v_h__1_451_, v_x_449_);
return v___x_453_;
}
else
{
lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v___x_456_; 
lean_dec(v_h__1_451_);
v_head_454_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_head_454_);
v_tail_455_ = lean_ctor_get(v_x_450_, 1);
lean_inc(v_tail_455_);
lean_dec_ref_known(v_x_450_, 2);
v___x_456_ = lean_apply_3(v_h__2_452_, v_x_449_, v_head_454_, v_tail_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(lean_object* v_motive_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_462_; 
lean_dec(v_h__2_461_);
v___x_462_ = lean_apply_1(v_h__1_460_, v_x_458_);
return v___x_462_;
}
else
{
lean_object* v_head_463_; lean_object* v_tail_464_; lean_object* v___x_465_; 
lean_dec(v_h__1_460_);
v_head_463_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_463_);
v_tail_464_ = lean_ctor_get(v_x_459_, 1);
lean_inc(v_tail_464_);
lean_dec_ref_known(v_x_459_, 2);
v___x_465_ = lean_apply_3(v_h__2_461_, v_x_458_, v_head_463_, v_tail_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(lean_object* v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_x_469_; lean_object* v___x_470_; 
lean_dec(v_h__2_468_);
v_x_469_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_x_469_);
lean_dec_ref_known(v_x_466_, 1);
v___x_470_ = lean_apply_1(v_h__1_467_, v_x_469_);
return v___x_470_;
}
else
{
lean_object* v_lhs_471_; lean_object* v_rhs_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_467_);
v_lhs_471_ = lean_ctor_get(v_x_466_, 0);
lean_inc_ref(v_lhs_471_);
v_rhs_472_ = lean_ctor_get(v_x_466_, 1);
lean_inc_ref(v_rhs_472_);
lean_dec_ref_known(v_x_466_, 2);
v___x_473_ = lean_apply_2(v_h__2_468_, v_lhs_471_, v_rhs_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(lean_object* v_motive_474_, lean_object* v_x_475_, lean_object* v_h__1_476_, lean_object* v_h__2_477_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v_x_478_; lean_object* v___x_479_; 
lean_dec(v_h__2_477_);
v_x_478_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_x_478_);
lean_dec_ref_known(v_x_475_, 1);
v___x_479_ = lean_apply_1(v_h__1_476_, v_x_478_);
return v___x_479_;
}
else
{
lean_object* v_lhs_480_; lean_object* v_rhs_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_476_);
v_lhs_480_ = lean_ctor_get(v_x_475_, 0);
lean_inc_ref(v_lhs_480_);
v_rhs_481_ = lean_ctor_get(v_x_475_, 1);
lean_inc_ref(v_rhs_481_);
lean_dec_ref_known(v_x_475_, 2);
v___x_482_ = lean_apply_2(v_h__2_477_, v_lhs_480_, v_rhs_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_h__1_484_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_apply_1(v_h__2_485_, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v_head_488_; lean_object* v_tail_489_; lean_object* v___x_490_; 
lean_dec(v_h__2_485_);
v_head_488_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_head_488_);
v_tail_489_ = lean_ctor_get(v_x_483_, 1);
lean_inc(v_tail_489_);
lean_dec_ref_known(v_x_483_, 2);
v___x_490_ = lean_apply_2(v_h__1_484_, v_head_488_, v_tail_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(lean_object* v_motive_491_, lean_object* v_x_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_h__1_493_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_1(v_h__2_494_, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v_tail_498_; lean_object* v___x_499_; 
lean_dec(v_h__2_494_);
v_head_497_ = lean_ctor_get(v_x_492_, 0);
lean_inc(v_head_497_);
v_tail_498_ = lean_ctor_get(v_x_492_, 1);
lean_inc(v_tail_498_);
lean_dec_ref_known(v_x_492_, 2);
v___x_499_ = lean_apply_2(v_h__1_493_, v_head_497_, v_tail_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(uint8_t v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
if (v_x_500_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_h__1_501_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_apply_1(v_h__2_502_, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_h__2_502_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_apply_1(v_h__1_501_, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
uint8_t v_x_24__boxed_510_; lean_object* v_res_511_; 
v_x_24__boxed_510_ = lean_unbox(v_x_507_);
v_res_511_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(v_x_24__boxed_510_, v_h__1_508_, v_h__2_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_object* v_motive_512_, uint8_t v_x_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
if (v_x_513_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_h__1_514_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_1(v_h__2_515_, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_h__2_515_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_h__1_514_, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(lean_object* v_motive_520_, lean_object* v_x_521_, lean_object* v_h__1_522_, lean_object* v_h__2_523_){
_start:
{
uint8_t v_x_35__boxed_524_; lean_object* v_res_525_; 
v_x_35__boxed_524_ = lean_unbox(v_x_521_);
v_res_525_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(v_motive_520_, v_x_35__boxed_524_, v_h__1_522_, v_h__2_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(lean_object* v_x_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_h__2_528_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_1(v_h__1_527_, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
lean_dec(v_h__1_527_);
v___x_531_ = lean_apply_2(v_h__2_528_, v_x_526_, lean_box(0));
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(lean_object* v_motive_532_, lean_object* v_x_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_h__2_535_);
v___x_536_ = lean_box(0);
v___x_537_ = lean_apply_1(v_h__1_534_, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; 
lean_dec(v_h__1_534_);
v___x_538_ = lean_apply_2(v_h__2_535_, v_x_533_, lean_box(0));
return v___x_538_;
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
