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
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___closed__0 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__0_value;
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___closed__1 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__1_value;
static const lean_closure_object l_Lean_Data_AC_instContextInformationContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instContextInformationContext___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instContextInformationContext___closed__2 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__2_value;
static const lean_ctor_object l_Lean_Data_AC_instContextInformationContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__0_value),((lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__1_value),((lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__2_value)}};
static const lean_object* l_Lean_Data_AC_instContextInformationContext___closed__3 = (const lean_object*)&l_Lean_Data_AC_instContextInformationContext___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___closed__0 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__0_value;
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___closed__1 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__1_value;
static const lean_closure_object l_Lean_Data_AC_instEvalInformationContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___closed__2 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__2_value;
static const lean_ctor_object l_Lean_Data_AC_instEvalInformationContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__0_value),((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__1_value),((lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__2_value)}};
static const lean_object* l_Lean_Data_AC_instEvalInformationContext___closed__3 = (const lean_object*)&l_Lean_Data_AC_instEvalInformationContext___closed__3_value;
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v___x_137_);
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
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__0(lean_object* v_ctx_152_, lean_object* v_x_153_){
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
lean_dec_ref(v_neutral_155_);
v___x_157_ = 1;
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__0___boxed(lean_object* v_ctx_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Data_AC_instContextInformationContext___lam__0(v_ctx_158_, v_x_159_);
lean_dec_ref(v_ctx_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__1(lean_object* v_ctx_162_){
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
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__1___boxed(lean_object* v_ctx_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Data_AC_instContextInformationContext___lam__1(v_ctx_166_);
lean_dec_ref(v_ctx_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Data_AC_instContextInformationContext___lam__2(lean_object* v_ctx_169_){
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
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext___lam__2___boxed(lean_object* v_ctx_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Data_AC_instContextInformationContext___lam__2(v_ctx_173_);
lean_dec_ref(v_ctx_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instContextInformationContext(lean_object* v_00_u03b1_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_Lean_Data_AC_instContextInformationContext___closed__3));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__0(lean_object* v_ctx_185_){
_start:
{
lean_object* v_arbitrary_186_; 
v_arbitrary_186_ = lean_ctor_get(v_ctx_185_, 4);
lean_inc(v_arbitrary_186_);
return v_arbitrary_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed(lean_object* v_ctx_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Data_AC_instEvalInformationContext___lam__0(v_ctx_187_);
lean_dec_ref(v_ctx_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__1(lean_object* v_ctx_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_op_192_; lean_object* v___x_193_; 
v_op_192_ = lean_ctor_get(v_ctx_189_, 0);
lean_inc(v_op_192_);
lean_dec_ref(v_ctx_189_);
v___x_193_ = lean_apply_2(v_op_192_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__2(lean_object* v_ctx_194_, lean_object* v_idx_195_){
_start:
{
lean_object* v___x_196_; lean_object* v_value_197_; 
v___x_196_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_194_, v_idx_195_);
v_value_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_value_197_);
lean_dec_ref(v___x_196_);
return v_value_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed(lean_object* v_ctx_198_, lean_object* v_idx_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Data_AC_instEvalInformationContext___lam__2(v_ctx_198_, v_idx_199_);
lean_dec_ref(v_ctx_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_instEvalInformationContext(lean_object* v_00_u03b1_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Lean_Data_AC_instEvalInformationContext___closed__3));
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval___redArg(lean_object* v_inst_210_, lean_object* v_ctx_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v_x_213_; lean_object* v_evalVar_214_; lean_object* v___x_215_; 
v_x_213_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_x_213_);
lean_dec_ref(v_x_212_);
v_evalVar_214_ = lean_ctor_get(v_inst_210_, 2);
lean_inc(v_evalVar_214_);
lean_dec_ref(v_inst_210_);
v___x_215_ = lean_apply_2(v_evalVar_214_, v_ctx_211_, v_x_213_);
return v___x_215_;
}
else
{
lean_object* v_lhs_216_; lean_object* v_rhs_217_; lean_object* v_evalOp_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_lhs_216_ = lean_ctor_get(v_x_212_, 0);
lean_inc_ref(v_lhs_216_);
v_rhs_217_ = lean_ctor_get(v_x_212_, 1);
lean_inc_ref(v_rhs_217_);
lean_dec_ref(v_x_212_);
v_evalOp_218_ = lean_ctor_get(v_inst_210_, 1);
lean_inc(v_evalOp_218_);
lean_inc_n(v_ctx_211_, 2);
lean_inc_ref(v_inst_210_);
v___x_219_ = l_Lean_Data_AC_eval___redArg(v_inst_210_, v_ctx_211_, v_lhs_216_);
v___x_220_ = l_Lean_Data_AC_eval___redArg(v_inst_210_, v_ctx_211_, v_rhs_217_);
v___x_221_ = lean_apply_3(v_evalOp_218_, v_ctx_211_, v___x_219_, v___x_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_eval(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_inst_224_, lean_object* v_ctx_225_, lean_object* v_x_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Data_AC_eval___redArg(v_inst_224_, v_ctx_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList(lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_x_229_ = lean_ctor_get(v_x_228_, 0);
v___x_230_ = lean_box(0);
lean_inc(v_x_229_);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v_x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
return v___x_231_;
}
else
{
lean_object* v_lhs_232_; lean_object* v_rhs_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_lhs_232_ = lean_ctor_get(v_x_228_, 0);
v_rhs_233_ = lean_ctor_get(v_x_228_, 1);
v___x_234_ = l_Lean_Data_AC_Expr_toList(v_lhs_232_);
v___x_235_ = l_Lean_Data_AC_Expr_toList(v_rhs_233_);
v___x_236_ = l_List_appendTR___redArg(v___x_234_, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_Expr_toList___boxed(lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Data_AC_Expr_toList(v_x_237_);
lean_dec_ref(v_x_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___redArg(lean_object* v_inst_239_, lean_object* v_ctx_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_arbitrary_242_; lean_object* v___x_243_; 
v_arbitrary_242_ = lean_ctor_get(v_inst_239_, 0);
lean_inc(v_arbitrary_242_);
lean_dec_ref(v_inst_239_);
v___x_243_ = lean_apply_1(v_arbitrary_242_, v_ctx_240_);
return v___x_243_;
}
else
{
lean_object* v_tail_244_; 
v_tail_244_ = lean_ctor_get(v_x_241_, 1);
if (lean_obj_tag(v_tail_244_) == 0)
{
lean_object* v_head_245_; lean_object* v_evalVar_246_; lean_object* v___x_247_; 
v_head_245_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_head_245_);
lean_dec_ref(v_x_241_);
v_evalVar_246_ = lean_ctor_get(v_inst_239_, 2);
lean_inc(v_evalVar_246_);
lean_dec_ref(v_inst_239_);
v___x_247_ = lean_apply_2(v_evalVar_246_, v_ctx_240_, v_head_245_);
return v___x_247_;
}
else
{
lean_object* v_head_248_; lean_object* v_evalOp_249_; lean_object* v_evalVar_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_inc(v_tail_244_);
v_head_248_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_head_248_);
lean_dec_ref(v_x_241_);
v_evalOp_249_ = lean_ctor_get(v_inst_239_, 1);
lean_inc(v_evalOp_249_);
v_evalVar_250_ = lean_ctor_get(v_inst_239_, 2);
lean_inc(v_evalVar_250_);
lean_inc_n(v_ctx_240_, 2);
v___x_251_ = lean_apply_2(v_evalVar_250_, v_ctx_240_, v_head_248_);
v___x_252_ = l_Lean_Data_AC_evalList___redArg(v_inst_239_, v_ctx_240_, v_tail_244_);
v___x_253_ = lean_apply_3(v_evalOp_249_, v_ctx_240_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_inst_256_, lean_object* v_ctx_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Data_AC_evalList___redArg(v_inst_256_, v_ctx_257_, v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_insert(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_x_260_);
lean_ctor_set(v___x_262_, 1, v_x_261_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; uint8_t v___x_265_; 
v_head_263_ = lean_ctor_get(v_x_261_, 0);
v_tail_264_ = lean_ctor_get(v_x_261_, 1);
v___x_265_ = lean_nat_dec_lt(v_x_260_, v_head_263_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
lean_inc(v_tail_264_);
lean_inc(v_head_263_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_274_ = lean_ctor_get(v_x_261_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_x_261_, 0);
lean_dec(v_unused_275_);
v___x_267_ = v_x_261_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_x_261_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_Data_AC_insert(v_x_260_, v_tail_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_head_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v_x_260_);
lean_ctor_set(v___x_276_, 1, v_x_261_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort_loop(lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
if (lean_obj_tag(v_a_278_) == 0)
{
return v_a_277_;
}
else
{
lean_object* v_head_279_; lean_object* v_tail_280_; lean_object* v___x_281_; 
v_head_279_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_head_279_);
v_tail_280_ = lean_ctor_get(v_a_278_, 1);
lean_inc(v_tail_280_);
lean_dec_ref(v_a_278_);
v___x_281_ = l_Lean_Data_AC_insert(v_head_279_, v_a_277_);
v_a_277_ = v___x_281_;
v_a_278_ = v_tail_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_sort(lean_object* v_xs_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(0);
v___x_285_ = l_Lean_Data_AC_sort_loop(v___x_284_, v_xs_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem_loop(lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
if (lean_obj_tag(v_a_287_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v_a_286_);
lean_ctor_set(v___x_288_, 1, v_a_287_);
return v___x_288_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_head_289_ = lean_ctor_get(v_a_287_, 0);
v_tail_290_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_300_ == 0)
{
v___x_292_ = v_a_287_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_tail_290_);
lean_inc(v_head_289_);
lean_dec(v_a_287_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_eq(v_a_286_, v_head_289_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_Data_AC_mergeIdem_loop(v_head_289_, v_tail_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_295_);
lean_ctor_set(v___x_292_, 0, v_a_286_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_del_object(v___x_292_);
lean_dec(v_head_289_);
v_a_287_ = v_tail_290_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_mergeIdem(lean_object* v_xs_301_){
_start:
{
if (lean_obj_tag(v_xs_301_) == 0)
{
return v_xs_301_;
}
else
{
lean_object* v_head_302_; lean_object* v_tail_303_; lean_object* v___x_304_; 
v_head_302_ = lean_ctor_get(v_xs_301_, 0);
lean_inc(v_head_302_);
v_tail_303_ = lean_ctor_get(v_xs_301_, 1);
lean_inc(v_tail_303_);
lean_dec_ref(v_xs_301_);
v___x_304_ = l_Lean_Data_AC_mergeIdem_loop(v_head_302_, v_tail_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___redArg(lean_object* v_info_305_, lean_object* v_ctx_306_, lean_object* v_a_307_){
_start:
{
if (lean_obj_tag(v_a_307_) == 0)
{
lean_dec(v_ctx_306_);
lean_dec_ref(v_info_305_);
return v_a_307_;
}
else
{
lean_object* v_head_308_; lean_object* v_tail_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_head_308_ = lean_ctor_get(v_a_307_, 0);
v_tail_309_ = lean_ctor_get(v_a_307_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_a_307_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_tail_309_);
lean_inc(v_head_308_);
lean_dec(v_a_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_isNeutral_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_isNeutral_313_ = lean_ctor_get(v_info_305_, 0);
lean_inc_ref(v_isNeutral_313_);
lean_inc(v_head_308_);
lean_inc(v_ctx_306_);
v___x_314_ = lean_apply_2(v_isNeutral_313_, v_ctx_306_, v_head_308_);
v___x_315_ = lean_unbox(v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_305_, v_ctx_306_, v_tail_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_316_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_head_308_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_del_object(v___x_311_);
lean_dec(v_head_308_);
v_a_307_ = v_tail_309_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop(lean_object* v_00_u03b1_322_, lean_object* v_info_323_, lean_object* v_ctx_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_323_, v_ctx_324_, v_a_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___redArg(lean_object* v_info_327_, lean_object* v_ctx_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_dec(v_ctx_328_);
lean_dec_ref(v_info_327_);
return v_x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v___x_331_; 
v_head_330_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_head_330_);
v___x_331_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_327_, v_ctx_328_, v_x_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_head_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
return v___x_332_;
}
else
{
lean_dec(v_head_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals(lean_object* v_00_u03b1_333_, lean_object* v_info_334_, lean_object* v_ctx_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_334_, v_ctx_335_, v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg(lean_object* v_info_338_, lean_object* v_ctx_339_, lean_object* v_e_340_){
_start:
{
lean_object* v_isComm_341_; lean_object* v_isIdem_342_; lean_object* v___y_344_; lean_object* v_xs_348_; lean_object* v_xs_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_isComm_341_ = lean_ctor_get(v_info_338_, 1);
lean_inc_ref(v_isComm_341_);
v_isIdem_342_ = lean_ctor_get(v_info_338_, 2);
lean_inc_ref(v_isIdem_342_);
v_xs_348_ = l_Lean_Data_AC_Expr_toList(v_e_340_);
lean_inc_n(v_ctx_339_, 2);
v_xs_349_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_338_, v_ctx_339_, v_xs_348_);
v___x_350_ = lean_apply_1(v_isComm_341_, v_ctx_339_);
v___x_351_ = lean_unbox(v___x_350_);
if (v___x_351_ == 0)
{
v___y_344_ = v_xs_349_;
goto v___jp_343_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Data_AC_sort(v_xs_349_);
v___y_344_ = v___x_352_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_apply_1(v_isIdem_342_, v_ctx_339_);
v___x_346_ = lean_unbox(v___x_345_);
if (v___x_346_ == 0)
{
return v___y_344_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Data_AC_mergeIdem(v___y_344_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___redArg___boxed(lean_object* v_info_353_, lean_object* v_ctx_354_, lean_object* v_e_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Data_AC_norm___redArg(v_info_353_, v_ctx_354_, v_e_355_);
lean_dec_ref(v_e_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm(lean_object* v_00_u03b1_357_, lean_object* v_info_358_, lean_object* v_ctx_359_, lean_object* v_e_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Data_AC_norm___redArg(v_info_358_, v_ctx_359_, v_e_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___boxed(lean_object* v_00_u03b1_362_, lean_object* v_info_363_, lean_object* v_ctx_364_, lean_object* v_e_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Data_AC_norm(v_00_u03b1_362_, v_info_363_, v_ctx_364_, v_e_365_);
lean_dec_ref(v_e_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_369_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_apply_1(v_h__1_368_, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_head_372_; lean_object* v_tail_373_; lean_object* v___x_374_; 
lean_dec(v_h__1_368_);
v_head_372_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_head_372_);
v_tail_373_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_tail_373_);
lean_dec_ref(v_x_367_);
v___x_374_ = lean_apply_2(v_h__2_369_, v_head_372_, v_tail_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(lean_object* v_motive_375_, lean_object* v_x_376_, lean_object* v_h__1_377_, lean_object* v_h__2_378_){
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
lean_dec_ref(v_x_376_);
v___x_383_ = lean_apply_2(v_h__2_378_, v_head_381_, v_tail_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v___x_388_; 
lean_dec(v_h__1_386_);
v___x_388_ = lean_apply_1(v_h__2_387_, v_x_384_);
return v___x_388_;
}
else
{
lean_object* v_head_389_; lean_object* v_tail_390_; lean_object* v___x_391_; 
lean_dec(v_h__2_387_);
v_head_389_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_head_389_);
v_tail_390_ = lean_ctor_get(v_x_385_, 1);
lean_inc(v_tail_390_);
lean_dec_ref(v_x_385_);
v___x_391_ = lean_apply_3(v_h__1_386_, v_x_384_, v_head_389_, v_tail_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(lean_object* v_motive_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_){
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
lean_dec_ref(v_x_394_);
v___x_400_ = lean_apply_3(v_h__1_395_, v_x_393_, v_head_398_, v_tail_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_h__1_402_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_apply_1(v_h__2_403_, v___x_404_);
return v___x_405_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_403_);
v_val_406_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v_x_401_);
v___x_407_ = lean_apply_1(v_h__1_402_, v_val_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_408_, lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
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
lean_dec_ref(v_x_410_);
v___x_416_ = lean_apply_1(v_h__1_411_, v_val_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_apply_1(v_h__1_418_, v___x_421_);
return v___x_422_;
}
else
{
lean_object* v_tail_423_; 
lean_dec(v_h__1_418_);
v_tail_423_ = lean_ctor_get(v_x_417_, 1);
if (lean_obj_tag(v_tail_423_) == 0)
{
lean_object* v_head_424_; lean_object* v___x_425_; 
lean_dec(v_h__3_420_);
v_head_424_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_424_);
lean_dec_ref(v_x_417_);
v___x_425_ = lean_apply_1(v_h__2_419_, v_head_424_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v___x_427_; 
lean_inc(v_tail_423_);
lean_dec(v_h__2_419_);
v_head_426_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_426_);
lean_dec_ref(v_x_417_);
v___x_427_ = lean_apply_3(v_h__3_420_, v_head_426_, v_tail_423_, lean_box(0));
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(lean_object* v_motive_428_, lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_, lean_object* v_h__3_432_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_432_);
lean_dec(v_h__2_431_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_1(v_h__1_430_, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v_tail_435_; 
lean_dec(v_h__1_430_);
v_tail_435_ = lean_ctor_get(v_x_429_, 1);
if (lean_obj_tag(v_tail_435_) == 0)
{
lean_object* v_head_436_; lean_object* v___x_437_; 
lean_dec(v_h__3_432_);
v_head_436_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_head_436_);
lean_dec_ref(v_x_429_);
v___x_437_ = lean_apply_1(v_h__2_431_, v_head_436_);
return v___x_437_;
}
else
{
lean_object* v_head_438_; lean_object* v___x_439_; 
lean_inc(v_tail_435_);
lean_dec(v_h__2_431_);
v_head_438_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_head_438_);
lean_dec_ref(v_x_429_);
v___x_439_ = lean_apply_3(v_h__3_432_, v_head_438_, v_tail_435_, lean_box(0));
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_h__1_442_, lean_object* v_h__2_443_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_444_; 
lean_dec(v_h__2_443_);
v___x_444_ = lean_apply_1(v_h__1_442_, v_x_440_);
return v___x_444_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_447_; 
lean_dec(v_h__1_442_);
v_head_445_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_head_445_);
v_tail_446_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_tail_446_);
lean_dec_ref(v_x_441_);
v___x_447_ = lean_apply_3(v_h__2_443_, v_x_440_, v_head_445_, v_tail_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(lean_object* v_motive_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
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
lean_dec_ref(v_x_450_);
v___x_456_ = lean_apply_3(v_h__2_452_, v_x_449_, v_head_454_, v_tail_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(lean_object* v_x_457_, lean_object* v_h__1_458_, lean_object* v_h__2_459_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v_x_460_; lean_object* v___x_461_; 
lean_dec(v_h__2_459_);
v_x_460_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_x_460_);
lean_dec_ref(v_x_457_);
v___x_461_ = lean_apply_1(v_h__1_458_, v_x_460_);
return v___x_461_;
}
else
{
lean_object* v_lhs_462_; lean_object* v_rhs_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_458_);
v_lhs_462_ = lean_ctor_get(v_x_457_, 0);
lean_inc_ref(v_lhs_462_);
v_rhs_463_ = lean_ctor_get(v_x_457_, 1);
lean_inc_ref(v_rhs_463_);
lean_dec_ref(v_x_457_);
v___x_464_ = lean_apply_2(v_h__2_459_, v_lhs_462_, v_rhs_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(lean_object* v_motive_465_, lean_object* v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_x_469_; lean_object* v___x_470_; 
lean_dec(v_h__2_468_);
v_x_469_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_x_469_);
lean_dec_ref(v_x_466_);
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
lean_dec_ref(v_x_466_);
v___x_473_ = lean_apply_2(v_h__2_468_, v_lhs_471_, v_rhs_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_h__1_475_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_apply_1(v_h__2_476_, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v_head_479_; lean_object* v_tail_480_; lean_object* v___x_481_; 
lean_dec(v_h__2_476_);
v_head_479_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_head_479_);
v_tail_480_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_tail_480_);
lean_dec_ref(v_x_474_);
v___x_481_ = lean_apply_2(v_h__1_475_, v_head_479_, v_tail_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(lean_object* v_motive_482_, lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
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
lean_dec_ref(v_x_483_);
v___x_490_ = lean_apply_2(v_h__1_484_, v_head_488_, v_tail_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(uint8_t v_x_491_, lean_object* v_h__1_492_, lean_object* v_h__2_493_){
_start:
{
if (v_x_491_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_h__1_492_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_apply_1(v_h__2_493_, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_h__2_493_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_apply_1(v_h__1_492_, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
uint8_t v_x_26__boxed_501_; lean_object* v_res_502_; 
v_x_26__boxed_501_ = lean_unbox(v_x_498_);
v_res_502_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(v_x_26__boxed_501_, v_h__1_499_, v_h__2_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(lean_object* v_motive_503_, uint8_t v_x_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
if (v_x_504_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_505_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__2_506_, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__1_505_, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(lean_object* v_motive_511_, lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
uint8_t v_x_37__boxed_515_; lean_object* v_res_516_; 
v_x_37__boxed_515_ = lean_unbox(v_x_512_);
v_res_516_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(v_motive_511_, v_x_37__boxed_515_, v_h__1_513_, v_h__2_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_519_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__1_518_, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_h__1_518_);
v___x_522_ = lean_apply_2(v_h__2_519_, v_x_517_, lean_box(0));
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(lean_object* v_motive_523_, lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_h__2_526_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_1(v_h__1_525_, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
lean_dec(v_h__1_525_);
v___x_529_ = lean_apply_2(v_h__2_526_, v_x_524_, lean_box(0));
return v___x_529_;
}
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
