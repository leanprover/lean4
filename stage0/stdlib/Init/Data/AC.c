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
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Data_AC_Expr_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_x_8_; lean_object* v___x_9_; 
v_x_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_x_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_x_8_);
return v___x_9_;
}
else
{
lean_object* v_lhs_10_; lean_object* v_rhs_11_; lean_object* v___x_12_; 
v_lhs_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_lhs_10_);
v_rhs_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_rhs_11_);
lean_dec_ref_known(v_t_6_, 2);
v___x_12_ = lean_apply_2(v_k_7_, v_lhs_10_, v_rhs_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Data_AC_Expr_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim___redArg(lean_object* v_t_25_, lean_object* v_var_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_25_, v_var_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_var_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_var_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_29_, v_var_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim___redArg(lean_object* v_t_33_, lean_object* v_op_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_33_, v_op_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_op_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_op_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_37_, v_op_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Data_AC_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(2u);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Data_AC_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr(lean_object* v_x_61_, lean_object* v_prec_62_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v_x_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_83_; 
v_x_63_ = lean_ctor_get(v_x_61_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_61_);
if (v_isSharedCheck_83_ == 0)
{
v___x_65_ = v_x_61_;
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_x_63_);
lean_dec(v_x_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_62_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__3, &l_Lean_Data_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__3);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__4, &l_Lean_Data_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__4);
v___y_68_ = v___x_82_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Lean_Data_AC_instReprExpr_repr___closed__2));
v___x_70_ = l_Nat_reprFast(v_x_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 3);
lean_ctor_set(v___x_65_, 0, v___x_70_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_78_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_69_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_inc(v___y_68_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_68_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_62_);
return v___x_77_;
}
}
}
}
else
{
lean_object* v_lhs_84_; lean_object* v_rhs_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_108_; 
v_lhs_84_ = lean_ctor_get(v_x_61_, 0);
v_rhs_85_ = lean_ctor_get(v_x_61_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_61_);
if (v_isSharedCheck_108_ == 0)
{
v___x_87_ = v_x_61_;
v_isShared_88_ = v_isSharedCheck_108_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_rhs_85_);
lean_inc(v_lhs_84_);
lean_dec(v_x_61_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_108_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___y_91_; uint8_t v___x_105_; 
v___x_89_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_89_, v_prec_62_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__3, &l_Lean_Data_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__3);
v___y_91_ = v___x_106_;
goto v___jp_90_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Data_AC_instReprExpr_repr___closed__4, &l_Lean_Data_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Data_AC_instReprExpr_repr___closed__4);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_92_ = lean_box(1);
v___x_93_ = ((lean_object*)(l_Lean_Data_AC_instReprExpr_repr___closed__7));
v___x_94_ = l_Lean_Data_AC_instReprExpr_repr(v_lhs_84_, v___x_89_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 5);
lean_ctor_set(v___x_87_, 1, v___x_94_);
lean_ctor_set(v___x_87_, 0, v___x_93_);
v___x_96_ = v___x_87_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_104_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_92_);
v___x_98_ = l_Lean_Data_AC_instReprExpr_repr(v_rhs_85_, v___x_89_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_inc(v___y_91_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___y_91_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_prec_62_);
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instReprExpr_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Data_AC_instReprExpr_repr(v_x_109_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instBEqExpr_beq(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_x_116_; lean_object* v_x_117_; uint8_t v___x_118_; 
v_x_116_ = lean_ctor_get(v_x_114_, 0);
v_x_117_ = lean_ctor_get(v_x_115_, 0);
v___x_118_ = lean_nat_dec_eq(v_x_116_, v_x_117_);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
else
{
if (lean_obj_tag(v_x_115_) == 1)
{
lean_object* v_lhs_120_; lean_object* v_rhs_121_; lean_object* v_lhs_122_; lean_object* v_rhs_123_; uint8_t v___x_124_; 
v_lhs_120_ = lean_ctor_get(v_x_114_, 0);
v_rhs_121_ = lean_ctor_get(v_x_114_, 1);
v_lhs_122_ = lean_ctor_get(v_x_115_, 0);
v_rhs_123_ = lean_ctor_get(v_x_115_, 1);
v___x_124_ = l_Lean_Data_AC_instBEqExpr_beq(v_lhs_120_, v_lhs_122_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
v_x_114_ = v_rhs_121_;
v_x_115_ = v_rhs_123_;
goto _start;
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(lean_object* v_ctx_152_, lean_object* v_x_153_){
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
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__0(v_ctx_158_, v_x_159_);
lean_dec_ref(v_ctx_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(lean_object* v_ctx_162_){
_start:
{
lean_object* v_comm_163_; 
v_comm_163_ = lean_ctor_get(v_ctx_162_, 1);
if (lean_obj_tag(v_comm_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = 1;
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__1___boxed(lean_object* v_ctx_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__1(v_ctx_166_);
lean_dec_ref(v_ctx_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(lean_object* v_ctx_169_){
_start:
{
lean_object* v_idem_170_; 
v_idem_170_ = lean_ctor_get(v_ctx_169_, 2);
if (lean_obj_tag(v_idem_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = 1;
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Data_AC_instContextInformationContext___redArg___lam__2(v_ctx_173_);
lean_dec_ref(v_ctx_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg(){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_Lean_Data_AC_instContextInformationContext___redArg___closed__3));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___redArg___boxed(lean_object* v___dummy_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Data_AC_instContextInformationContext___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Data_AC_instContextInformationContext___redArg();
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object* v_00_u03b1_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Data_AC_instContextInformationContext___closed__0, &l_Lean_Data_AC_instContextInformationContext___closed__0_once, _init_l_Lean_Data_AC_instContextInformationContext___closed__0);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(lean_object* v_ctx_190_){
_start:
{
lean_object* v_arbitrary_191_; 
v_arbitrary_191_ = lean_ctor_get(v_ctx_190_, 4);
lean_inc(v_arbitrary_191_);
return v_arbitrary_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0___boxed(lean_object* v_ctx_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__0(v_ctx_192_);
lean_dec_ref(v_ctx_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__1(lean_object* v_ctx_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_op_197_; lean_object* v___x_198_; 
v_op_197_ = lean_ctor_get(v_ctx_194_, 0);
lean_inc(v_op_197_);
lean_dec_ref(v_ctx_194_);
v___x_198_ = lean_apply_2(v_op_197_, v___y_195_, v___y_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(lean_object* v_ctx_199_, lean_object* v_idx_200_){
_start:
{
lean_object* v___x_201_; lean_object* v_value_202_; 
v___x_201_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_199_, v_idx_200_);
v_value_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_value_202_);
lean_dec_ref(v___x_201_);
return v_value_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2___boxed(lean_object* v_ctx_203_, lean_object* v_idx_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Data_AC_instEvalInformationContext___redArg___lam__2(v_ctx_203_, v_idx_204_);
lean_dec_ref(v_ctx_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg(){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Lean_Data_AC_instEvalInformationContext___redArg___closed__3));
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___redArg___boxed(lean_object* v___dummy_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v_res_216_;
}
}
static lean_object* _init_l_Lean_Data_AC_instEvalInformationContext___closed__0(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Data_AC_instEvalInformationContext___redArg();
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext(lean_object* v_00_u03b1_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lean_Data_AC_instEvalInformationContext___closed__0, &l_Lean_Data_AC_instEvalInformationContext___closed__0_once, _init_l_Lean_Data_AC_instEvalInformationContext___closed__0);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval___redArg(lean_object* v_inst_220_, lean_object* v_ctx_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v_x_223_; lean_object* v_evalVar_224_; lean_object* v___x_225_; 
v_x_223_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_x_223_);
lean_dec_ref_known(v_x_222_, 1);
v_evalVar_224_ = lean_ctor_get(v_inst_220_, 2);
lean_inc(v_evalVar_224_);
lean_dec_ref(v_inst_220_);
v___x_225_ = lean_apply_2(v_evalVar_224_, v_ctx_221_, v_x_223_);
return v___x_225_;
}
else
{
lean_object* v_lhs_226_; lean_object* v_rhs_227_; lean_object* v_evalOp_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_lhs_226_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_lhs_226_);
v_rhs_227_ = lean_ctor_get(v_x_222_, 1);
lean_inc_ref(v_rhs_227_);
lean_dec_ref_known(v_x_222_, 2);
v_evalOp_228_ = lean_ctor_get(v_inst_220_, 1);
lean_inc(v_evalOp_228_);
lean_inc_n(v_ctx_221_, 2);
lean_inc_ref(v_inst_220_);
v___x_229_ = l_Lean_Data_AC_eval___redArg(v_inst_220_, v_ctx_221_, v_lhs_226_);
v___x_230_ = l_Lean_Data_AC_eval___redArg(v_inst_220_, v_ctx_221_, v_rhs_227_);
v___x_231_ = lean_apply_3(v_evalOp_228_, v_ctx_221_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_inst_234_, lean_object* v_ctx_235_, lean_object* v_x_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Data_AC_eval___redArg(v_inst_234_, v_ctx_235_, v_x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList(lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_object* v_x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_x_239_ = lean_ctor_get(v_x_238_, 0);
v___x_240_ = lean_box(0);
lean_inc(v_x_239_);
v___x_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_241_, 0, v_x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_lhs_242_; lean_object* v_rhs_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_lhs_242_ = lean_ctor_get(v_x_238_, 0);
v_rhs_243_ = lean_ctor_get(v_x_238_, 1);
v___x_244_ = l_Lean_Data_AC_Expr_toList(v_lhs_242_);
v___x_245_ = l_Lean_Data_AC_Expr_toList(v_rhs_243_);
v___x_246_ = l_List_appendTR___redArg(v___x_244_, v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList___boxed(lean_object* v_x_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Data_AC_Expr_toList(v_x_247_);
lean_dec_ref(v_x_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___redArg(lean_object* v_inst_249_, lean_object* v_ctx_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v_arbitrary_252_; lean_object* v___x_253_; 
v_arbitrary_252_ = lean_ctor_get(v_inst_249_, 0);
lean_inc(v_arbitrary_252_);
lean_dec_ref(v_inst_249_);
v___x_253_ = lean_apply_1(v_arbitrary_252_, v_ctx_250_);
return v___x_253_;
}
else
{
lean_object* v_tail_254_; 
v_tail_254_ = lean_ctor_get(v_x_251_, 1);
if (lean_obj_tag(v_tail_254_) == 0)
{
lean_object* v_head_255_; lean_object* v_evalVar_256_; lean_object* v___x_257_; 
v_head_255_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_head_255_);
lean_dec_ref_known(v_x_251_, 2);
v_evalVar_256_ = lean_ctor_get(v_inst_249_, 2);
lean_inc(v_evalVar_256_);
lean_dec_ref(v_inst_249_);
v___x_257_ = lean_apply_2(v_evalVar_256_, v_ctx_250_, v_head_255_);
return v___x_257_;
}
else
{
lean_object* v_head_258_; lean_object* v_evalOp_259_; lean_object* v_evalVar_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_tail_254_);
v_head_258_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_head_258_);
lean_dec_ref_known(v_x_251_, 2);
v_evalOp_259_ = lean_ctor_get(v_inst_249_, 1);
lean_inc(v_evalOp_259_);
v_evalVar_260_ = lean_ctor_get(v_inst_249_, 2);
lean_inc(v_evalVar_260_);
lean_inc_n(v_ctx_250_, 2);
v___x_261_ = lean_apply_2(v_evalVar_260_, v_ctx_250_, v_head_258_);
v___x_262_ = l_Lean_Data_AC_evalList___redArg(v_inst_249_, v_ctx_250_, v_tail_254_);
v___x_263_ = lean_apply_3(v_evalOp_259_, v_ctx_250_, v___x_261_, v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_inst_266_, lean_object* v_ctx_267_, lean_object* v_x_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Data_AC_evalList___redArg(v_inst_266_, v_ctx_267_, v_x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_insert(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v_x_270_);
lean_ctor_set(v___x_272_, 1, v_x_271_);
return v___x_272_;
}
else
{
lean_object* v_head_273_; lean_object* v_tail_274_; uint8_t v___x_275_; 
v_head_273_ = lean_ctor_get(v_x_271_, 0);
v_tail_274_ = lean_ctor_get(v_x_271_, 1);
v___x_275_ = lean_nat_dec_lt(v_x_270_, v_head_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
lean_inc(v_tail_274_);
lean_inc(v_head_273_);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_284_ = lean_ctor_get(v_x_271_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_x_271_, 0);
lean_dec(v_unused_285_);
v___x_277_ = v_x_271_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_dec(v_x_271_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = l_Lean_Data_AC_insert(v_x_270_, v_tail_274_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_head_273_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v_x_270_);
lean_ctor_set(v___x_286_, 1, v_x_271_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort_loop(lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
if (lean_obj_tag(v_a_288_) == 0)
{
return v_a_287_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v___x_291_; 
v_head_289_ = lean_ctor_get(v_a_288_, 0);
lean_inc(v_head_289_);
v_tail_290_ = lean_ctor_get(v_a_288_, 1);
lean_inc(v_tail_290_);
lean_dec_ref_known(v_a_288_, 2);
v___x_291_ = l_Lean_Data_AC_insert(v_head_289_, v_a_287_);
v_a_287_ = v___x_291_;
v_a_288_ = v_tail_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort(lean_object* v_xs_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = l_Lean_Data_AC_sort_loop(v___x_294_, v_xs_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem_loop(lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_a_296_);
lean_ctor_set(v___x_298_, 1, v_a_297_);
return v___x_298_;
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_head_299_ = lean_ctor_get(v_a_297_, 0);
v_tail_300_ = lean_ctor_get(v_a_297_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_a_297_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_a_297_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_tail_300_);
lean_inc(v_head_299_);
lean_dec(v_a_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_eq(v_a_296_, v_head_299_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_Data_AC_mergeIdem_loop(v_head_299_, v_tail_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_305_);
lean_ctor_set(v___x_302_, 0, v_a_296_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_296_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
lean_del_object(v___x_302_);
lean_dec(v_head_299_);
v_a_297_ = v_tail_300_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem(lean_object* v_xs_311_){
_start:
{
if (lean_obj_tag(v_xs_311_) == 0)
{
return v_xs_311_;
}
else
{
lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v___x_314_; 
v_head_312_ = lean_ctor_get(v_xs_311_, 0);
lean_inc(v_head_312_);
v_tail_313_ = lean_ctor_get(v_xs_311_, 1);
lean_inc(v_tail_313_);
lean_dec_ref_known(v_xs_311_, 2);
v___x_314_ = l_Lean_Data_AC_mergeIdem_loop(v_head_312_, v_tail_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___redArg(lean_object* v_info_315_, lean_object* v_ctx_316_, lean_object* v_a_317_){
_start:
{
if (lean_obj_tag(v_a_317_) == 0)
{
lean_dec(v_ctx_316_);
lean_dec_ref(v_info_315_);
return v_a_317_;
}
else
{
lean_object* v_head_318_; lean_object* v_tail_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_head_318_ = lean_ctor_get(v_a_317_, 0);
v_tail_319_ = lean_ctor_get(v_a_317_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v_a_317_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_tail_319_);
lean_inc(v_head_318_);
lean_dec(v_a_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_isNeutral_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_isNeutral_323_ = lean_ctor_get(v_info_315_, 0);
lean_inc_ref(v_isNeutral_323_);
lean_inc(v_head_318_);
lean_inc(v_ctx_316_);
v___x_324_ = lean_apply_2(v_isNeutral_323_, v_ctx_316_, v_head_318_);
v___x_325_ = lean_unbox(v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_315_, v_ctx_316_, v_tail_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_326_);
v___x_328_ = v___x_321_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_head_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
lean_del_object(v___x_321_);
lean_dec(v_head_318_);
v_a_317_ = v_tail_319_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop(lean_object* v_00_u03b1_332_, lean_object* v_info_333_, lean_object* v_ctx_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_333_, v_ctx_334_, v_a_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___redArg(lean_object* v_info_337_, lean_object* v_ctx_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_dec(v_ctx_338_);
lean_dec_ref(v_info_337_);
return v_x_339_;
}
else
{
lean_object* v_head_340_; lean_object* v___x_341_; 
v_head_340_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_head_340_);
v___x_341_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_337_, v_ctx_338_, v_x_339_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v_head_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
return v___x_342_;
}
else
{
lean_dec(v_head_340_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals(lean_object* v_00_u03b1_343_, lean_object* v_info_344_, lean_object* v_ctx_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_344_, v_ctx_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg(lean_object* v_info_348_, lean_object* v_ctx_349_, lean_object* v_e_350_){
_start:
{
lean_object* v_isComm_351_; lean_object* v_isIdem_352_; lean_object* v___y_354_; lean_object* v_xs_358_; lean_object* v_xs_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_isComm_351_ = lean_ctor_get(v_info_348_, 1);
lean_inc_ref(v_isComm_351_);
v_isIdem_352_ = lean_ctor_get(v_info_348_, 2);
lean_inc_ref(v_isIdem_352_);
v_xs_358_ = l_Lean_Data_AC_Expr_toList(v_e_350_);
lean_inc_n(v_ctx_349_, 2);
v_xs_359_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_348_, v_ctx_349_, v_xs_358_);
v___x_360_ = lean_apply_1(v_isComm_351_, v_ctx_349_);
v___x_361_ = lean_unbox(v___x_360_);
if (v___x_361_ == 0)
{
v___y_354_ = v_xs_359_;
goto v___jp_353_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Data_AC_sort(v_xs_359_);
v___y_354_ = v___x_362_;
goto v___jp_353_;
}
v___jp_353_:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_apply_1(v_isIdem_352_, v_ctx_349_);
v___x_356_ = lean_unbox(v___x_355_);
if (v___x_356_ == 0)
{
return v___y_354_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Data_AC_mergeIdem(v___y_354_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg___boxed(lean_object* v_info_363_, lean_object* v_ctx_364_, lean_object* v_e_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Data_AC_norm___redArg(v_info_363_, v_ctx_364_, v_e_365_);
lean_dec_ref(v_e_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm(lean_object* v_00_u03b1_367_, lean_object* v_info_368_, lean_object* v_ctx_369_, lean_object* v_e_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Data_AC_norm___redArg(v_info_368_, v_ctx_369_, v_e_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___boxed(lean_object* v_00_u03b1_372_, lean_object* v_info_373_, lean_object* v_ctx_374_, lean_object* v_e_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Data_AC_norm(v_00_u03b1_372_, v_info_373_, v_ctx_374_, v_e_375_);
lean_dec_ref(v_e_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_h__2_379_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_apply_1(v_h__1_378_, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v_head_382_; lean_object* v_tail_383_; lean_object* v___x_384_; 
lean_dec(v_h__1_378_);
v_head_382_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_head_382_);
v_tail_383_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_tail_383_);
lean_dec_ref_known(v_x_377_, 2);
v___x_384_ = lean_apply_2(v_h__2_379_, v_head_382_, v_tail_383_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(lean_object* v_motive_385_, lean_object* v_x_386_, lean_object* v_h__1_387_, lean_object* v_h__2_388_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_h__2_388_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_apply_1(v_h__1_387_, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v_head_391_; lean_object* v_tail_392_; lean_object* v___x_393_; 
lean_dec(v_h__1_387_);
v_head_391_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_head_391_);
v_tail_392_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_tail_392_);
lean_dec_ref_known(v_x_386_, 2);
v___x_393_ = lean_apply_2(v_h__2_388_, v_head_391_, v_tail_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_398_; 
lean_dec(v_h__1_396_);
v___x_398_ = lean_apply_1(v_h__2_397_, v_x_394_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; 
lean_dec(v_h__2_397_);
v_head_399_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_head_399_);
v_tail_400_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_tail_400_);
lean_dec_ref_known(v_x_395_, 2);
v___x_401_ = lean_apply_3(v_h__1_396_, v_x_394_, v_head_399_, v_tail_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(lean_object* v_motive_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_h__1_405_, lean_object* v_h__2_406_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v___x_407_; 
lean_dec(v_h__1_405_);
v___x_407_ = lean_apply_1(v_h__2_406_, v_x_403_);
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v___x_410_; 
lean_dec(v_h__2_406_);
v_head_408_ = lean_ctor_get(v_x_404_, 0);
lean_inc(v_head_408_);
v_tail_409_ = lean_ctor_get(v_x_404_, 1);
lean_inc(v_tail_409_);
lean_dec_ref_known(v_x_404_, 2);
v___x_410_ = lean_apply_3(v_h__1_405_, v_x_403_, v_head_408_, v_tail_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_h__1_412_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_apply_1(v_h__2_413_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_417_; 
lean_dec(v_h__2_413_);
v_val_416_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_val_416_);
lean_dec_ref_known(v_x_411_, 1);
v___x_417_ = lean_apply_1(v_h__1_412_, v_val_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_418_, lean_object* v_motive_419_, lean_object* v_x_420_, lean_object* v_h__1_421_, lean_object* v_h__2_422_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_h__1_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_1(v_h__2_422_, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_422_);
v_val_425_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_x_420_, 1);
v___x_426_ = lean_apply_1(v_h__1_421_, v_val_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object* v_x_427_, lean_object* v_h__1_428_, lean_object* v_h__2_429_, lean_object* v_h__3_430_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_h__3_430_);
lean_dec(v_h__2_429_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_apply_1(v_h__1_428_, v___x_431_);
return v___x_432_;
}
else
{
lean_object* v_tail_433_; 
lean_dec(v_h__1_428_);
v_tail_433_ = lean_ctor_get(v_x_427_, 1);
if (lean_obj_tag(v_tail_433_) == 0)
{
lean_object* v_head_434_; lean_object* v___x_435_; 
lean_dec(v_h__3_430_);
v_head_434_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_head_434_);
lean_dec_ref_known(v_x_427_, 2);
v___x_435_ = lean_apply_1(v_h__2_429_, v_head_434_);
return v___x_435_;
}
else
{
lean_object* v_head_436_; lean_object* v___x_437_; 
lean_inc(v_tail_433_);
lean_dec(v_h__2_429_);
v_head_436_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_head_436_);
lean_dec_ref_known(v_x_427_, 2);
v___x_437_ = lean_apply_3(v_h__3_430_, v_head_436_, v_tail_433_, lean_box(0));
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object* v_motive_438_, lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_h__1_440_, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_tail_445_; 
lean_dec(v_h__1_440_);
v_tail_445_ = lean_ctor_get(v_x_439_, 1);
if (lean_obj_tag(v_tail_445_) == 0)
{
lean_object* v_head_446_; lean_object* v___x_447_; 
lean_dec(v_h__3_442_);
v_head_446_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_head_446_);
lean_dec_ref_known(v_x_439_, 2);
v___x_447_ = lean_apply_1(v_h__2_441_, v_head_446_);
return v___x_447_;
}
else
{
lean_object* v_head_448_; lean_object* v___x_449_; 
lean_inc(v_tail_445_);
lean_dec(v_h__2_441_);
v_head_448_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_head_448_);
lean_dec_ref_known(v_x_439_, 2);
v___x_449_ = lean_apply_3(v_h__3_442_, v_head_448_, v_tail_445_, lean_box(0));
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_454_; 
lean_dec(v_h__2_453_);
v___x_454_ = lean_apply_1(v_h__1_452_, v_x_450_);
return v___x_454_;
}
else
{
lean_object* v_head_455_; lean_object* v_tail_456_; lean_object* v___x_457_; 
lean_dec(v_h__1_452_);
v_head_455_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_head_455_);
v_tail_456_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_tail_456_);
lean_dec_ref_known(v_x_451_, 2);
v___x_457_ = lean_apply_3(v_h__2_453_, v_x_450_, v_head_455_, v_tail_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(lean_object* v_motive_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_463_; 
lean_dec(v_h__2_462_);
v___x_463_ = lean_apply_1(v_h__1_461_, v_x_459_);
return v___x_463_;
}
else
{
lean_object* v_head_464_; lean_object* v_tail_465_; lean_object* v___x_466_; 
lean_dec(v_h__1_461_);
v_head_464_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_head_464_);
v_tail_465_ = lean_ctor_get(v_x_460_, 1);
lean_inc(v_tail_465_);
lean_dec_ref_known(v_x_460_, 2);
v___x_466_ = lean_apply_3(v_h__2_462_, v_x_459_, v_head_464_, v_tail_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v_x_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_469_);
v_x_470_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_x_470_);
lean_dec_ref_known(v_x_467_, 1);
v___x_471_ = lean_apply_1(v_h__1_468_, v_x_470_);
return v___x_471_;
}
else
{
lean_object* v_lhs_472_; lean_object* v_rhs_473_; lean_object* v___x_474_; 
lean_dec(v_h__1_468_);
v_lhs_472_ = lean_ctor_get(v_x_467_, 0);
lean_inc_ref(v_lhs_472_);
v_rhs_473_ = lean_ctor_get(v_x_467_, 1);
lean_inc_ref(v_rhs_473_);
lean_dec_ref_known(v_x_467_, 2);
v___x_474_ = lean_apply_2(v_h__2_469_, v_lhs_472_, v_rhs_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(lean_object* v_motive_475_, lean_object* v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_x_479_; lean_object* v___x_480_; 
lean_dec(v_h__2_478_);
v_x_479_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_x_479_);
lean_dec_ref_known(v_x_476_, 1);
v___x_480_ = lean_apply_1(v_h__1_477_, v_x_479_);
return v___x_480_;
}
else
{
lean_object* v_lhs_481_; lean_object* v_rhs_482_; lean_object* v___x_483_; 
lean_dec(v_h__1_477_);
v_lhs_481_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_lhs_481_);
v_rhs_482_ = lean_ctor_get(v_x_476_, 1);
lean_inc_ref(v_rhs_482_);
lean_dec_ref_known(v_x_476_, 2);
v___x_483_ = lean_apply_2(v_h__2_478_, v_lhs_481_, v_rhs_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_h__1_485_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_apply_1(v_h__2_486_, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v_head_489_; lean_object* v_tail_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_486_);
v_head_489_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_head_489_);
v_tail_490_ = lean_ctor_get(v_x_484_, 1);
lean_inc(v_tail_490_);
lean_dec_ref_known(v_x_484_, 2);
v___x_491_ = lean_apply_2(v_h__1_485_, v_head_489_, v_tail_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(lean_object* v_motive_492_, lean_object* v_x_493_, lean_object* v_h__1_494_, lean_object* v_h__2_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_h__1_494_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_apply_1(v_h__2_495_, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v_head_498_; lean_object* v_tail_499_; lean_object* v___x_500_; 
lean_dec(v_h__2_495_);
v_head_498_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_head_498_);
v_tail_499_ = lean_ctor_get(v_x_493_, 1);
lean_inc(v_tail_499_);
lean_dec_ref_known(v_x_493_, 2);
v___x_500_ = lean_apply_2(v_h__1_494_, v_head_498_, v_tail_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(uint8_t v_x_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
if (v_x_501_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_h__1_502_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_apply_1(v_h__2_503_, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_h__2_503_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_apply_1(v_h__1_502_, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
uint8_t v_x_24__boxed_511_; lean_object* v_res_512_; 
v_x_24__boxed_511_ = lean_unbox(v_x_508_);
v_res_512_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(v_x_24__boxed_511_, v_h__1_509_, v_h__2_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_object* v_motive_513_, uint8_t v_x_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
if (v_x_514_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_h__1_515_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v_h__2_516_, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_h__2_516_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_1(v_h__1_515_, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(lean_object* v_motive_521_, lean_object* v_x_522_, lean_object* v_h__1_523_, lean_object* v_h__2_524_){
_start:
{
uint8_t v_x_35__boxed_525_; lean_object* v_res_526_; 
v_x_35__boxed_525_ = lean_unbox(v_x_522_);
v_res_526_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(v_motive_521_, v_x_35__boxed_525_, v_h__1_523_, v_h__2_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(lean_object* v_x_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v_h__2_529_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_apply_1(v_h__1_528_, v___x_530_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v_h__1_528_);
v___x_532_ = lean_apply_2(v_h__2_529_, v_x_527_, lean_box(0));
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(lean_object* v_motive_533_, lean_object* v_x_534_, lean_object* v_h__1_535_, lean_object* v_h__2_536_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_536_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__1_535_, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
lean_dec(v_h__1_535_);
v___x_539_ = lean_apply_2(v_h__2_536_, v_x_534_, lean_box(0));
return v___x_539_;
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
