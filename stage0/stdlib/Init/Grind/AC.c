// Lean compiler output
// Module: Init.Grind.AC
// Imports: public import Init.Data.Bool import Init.LawfulBEqTactics public import Init.Data.RArray import Init.Classical
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instInhabitedExpr_default = (const lean_object*)&l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instInhabitedExpr = (const lean_object*)&l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value;
static const lean_string_object l_Lean_Grind_AC_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Grind.AC.Expr.var"};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__1_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__2 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__2_value;
static lean_once_cell_t l_Lean_Grind_AC_instReprExpr_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__3;
static lean_once_cell_t l_Lean_Grind_AC_instReprExpr_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__4;
static const lean_string_object l_Lean_Grind_AC_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Grind.AC.Expr.op"};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__5_value)}};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_AC_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instReprExpr___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instReprExpr = (const lean_object*)&l_Lean_Grind_AC_instReprExpr___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_AC_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instBEqExpr___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instBEqExpr = (const lean_object*)&l_Lean_Grind_AC_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instInhabitedSeq_default___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instInhabitedSeq_default = (const lean_object*)&l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instInhabitedSeq = (const lean_object*)&l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value;
static const lean_string_object l_Lean_Grind_AC_instReprSeq_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Grind.AC.Seq.var"};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprSeq_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__1 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__1_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprSeq_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__2 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__2_value;
static const lean_string_object l_Lean_Grind_AC_instReprSeq_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Grind.AC.Seq.cons"};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__3 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__3_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprSeq_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__3_value)}};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__4 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__4_value;
static const lean_ctor_object l_Lean_Grind_AC_instReprSeq_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_instReprSeq_repr___closed__5 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_AC_instReprSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_instReprSeq_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instReprSeq___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instReprSeq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instReprSeq = (const lean_object*)&l_Lean_Grind_AC_instReprSeq___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqSeq_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_AC_instBEqSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_instBEqSeq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instBEqSeq___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instBEqSeq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instBEqSeq = (const lean_object*)&l_Lean_Grind_AC_instBEqSeq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_erase0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_eraseDup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_concat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_hugeFuel;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Grind_AC_Expr_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Grind_AC_Expr_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim___redArg(lean_object* v_t_24_, lean_object* v_var_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_24_, v_var_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_var_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_28_, v_var_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim___redArg(lean_object* v_t_32_, lean_object* v_op_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_32_, v_op_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_op_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_36_, v_op_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(2u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr(lean_object* v_x_60_, lean_object* v_prec_61_){
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
v___x_80_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_67_ = v___x_80_;
goto v___jp_66_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_67_ = v___x_81_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = ((lean_object*)(l_Lean_Grind_AC_instReprExpr_repr___closed__2));
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
v___x_105_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_90_ = v___x_105_;
goto v___jp_89_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_90_ = v___x_106_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_91_ = lean_box(1);
v___x_92_ = ((lean_object*)(l_Lean_Grind_AC_instReprExpr_repr___closed__7));
v___x_93_ = l_Lean_Grind_AC_instReprExpr_repr(v_lhs_83_, v___x_88_);
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
v___x_97_ = l_Lean_Grind_AC_instReprExpr_repr(v_rhs_84_, v___x_88_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr___boxed(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Grind_AC_instReprExpr_repr(v_x_108_, v_prec_109_);
lean_dec(v_prec_109_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqExpr_beq(lean_object* v_x_113_, lean_object* v_x_114_){
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
v___x_123_ = l_Lean_Grind_AC_instBEqExpr_beq(v_lhs_119_, v_lhs_121_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqExpr_beq___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Grind_AC_instBEqExpr_beq(v_x_126_, v_x_127_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___impl(lean_object* v_x_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_tag_nat(v_x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___impl___boxed(lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Grind_AC_Seq_ctorIdx___impl(v_x_134_);
lean_dec_ref(v_x_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___redArg(lean_object* v_t_136_, lean_object* v_k_137_){
_start:
{
if (lean_obj_tag(v_t_136_) == 0)
{
lean_object* v_x_138_; lean_object* v___x_139_; 
v_x_138_ = lean_ctor_get(v_t_136_, 0);
lean_inc(v_x_138_);
lean_dec_ref_known(v_t_136_, 1);
v___x_139_ = lean_apply_1(v_k_137_, v_x_138_);
return v___x_139_;
}
else
{
lean_object* v_x_140_; lean_object* v_s_141_; lean_object* v___x_142_; 
v_x_140_ = lean_ctor_get(v_t_136_, 0);
lean_inc(v_x_140_);
v_s_141_ = lean_ctor_get(v_t_136_, 1);
lean_inc_ref(v_s_141_);
lean_dec_ref_known(v_t_136_, 2);
v___x_142_ = lean_apply_2(v_k_137_, v_x_140_, v_s_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim(lean_object* v_motive_143_, lean_object* v_ctorIdx_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_k_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_145_, v_k_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___boxed(lean_object* v_motive_149_, lean_object* v_ctorIdx_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_k_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Grind_AC_Seq_ctorElim(v_motive_149_, v_ctorIdx_150_, v_t_151_, v_h_152_, v_k_153_);
lean_dec(v_ctorIdx_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim___redArg(lean_object* v_t_155_, lean_object* v_var_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_155_, v_var_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_var_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_159_, v_var_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim___redArg(lean_object* v_t_163_, lean_object* v_cons_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_163_, v_cons_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_cons_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_167_, v_cons_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr(lean_object* v_x_187_, lean_object* v_prec_188_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_x_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_209_; 
v_x_189_ = lean_ctor_get(v_x_187_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_209_ == 0)
{
v___x_191_ = v_x_187_;
v_isShared_192_ = v_isSharedCheck_209_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_x_189_);
lean_dec(v_x_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_209_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___y_194_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1024u);
v___x_206_ = lean_nat_dec_le(v___x_205_, v_prec_188_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_194_ = v___x_207_;
goto v___jp_193_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_194_ = v___x_208_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = ((lean_object*)(l_Lean_Grind_AC_instReprSeq_repr___closed__2));
v___x_196_ = l_Nat_reprFast(v_x_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 3);
lean_ctor_set(v___x_191_, 0, v___x_196_);
v___x_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_204_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_195_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_inc(v___y_194_);
v___x_200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_194_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = 0;
v___x_202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_201_);
v___x_203_ = l_Repr_addAppParen(v___x_202_, v_prec_188_);
return v___x_203_;
}
}
}
}
else
{
lean_object* v_x_210_; lean_object* v_s_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_235_; 
v_x_210_ = lean_ctor_get(v_x_187_, 0);
v_s_211_ = lean_ctor_get(v_x_187_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_235_ == 0)
{
v___x_213_ = v_x_187_;
v_isShared_214_ = v_isSharedCheck_235_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_s_211_);
lean_inc(v_x_210_);
lean_dec(v_x_187_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_235_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___y_217_; uint8_t v___x_232_; 
v___x_215_ = lean_unsigned_to_nat(1024u);
v___x_232_ = lean_nat_dec_le(v___x_215_, v_prec_188_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_217_ = v___x_233_;
goto v___jp_216_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_217_ = v___x_234_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_218_ = lean_box(1);
v___x_219_ = ((lean_object*)(l_Lean_Grind_AC_instReprSeq_repr___closed__5));
v___x_220_ = l_Nat_reprFast(v_x_210_);
v___x_221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 5);
lean_ctor_set(v___x_213_, 1, v___x_221_);
lean_ctor_set(v___x_213_, 0, v___x_219_);
v___x_223_ = v___x_213_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_231_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_218_);
v___x_225_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_211_, v___x_215_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_inc(v___y_217_);
v___x_227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_217_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_228_);
v___x_230_ = l_Repr_addAppParen(v___x_229_, v_prec_188_);
return v___x_230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr___boxed(lean_object* v_x_236_, lean_object* v_prec_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Grind_AC_instReprSeq_repr(v_x_236_, v_prec_237_);
lean_dec(v_prec_237_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v_x_243_; lean_object* v_x_244_; uint8_t v___x_245_; 
v_x_243_ = lean_ctor_get(v_x_241_, 0);
v_x_244_ = lean_ctor_get(v_x_242_, 0);
v___x_245_ = lean_nat_dec_eq(v_x_243_, v_x_244_);
return v___x_245_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
}
else
{
if (lean_obj_tag(v_x_242_) == 1)
{
lean_object* v_x_247_; lean_object* v_s_248_; lean_object* v_x_249_; lean_object* v_s_250_; uint8_t v___x_251_; 
v_x_247_ = lean_ctor_get(v_x_241_, 0);
v_s_248_ = lean_ctor_get(v_x_241_, 1);
v_x_249_ = lean_ctor_get(v_x_242_, 0);
v_s_250_ = lean_ctor_get(v_x_242_, 1);
v___x_251_ = lean_nat_dec_eq(v_x_247_, v_x_249_);
if (v___x_251_ == 0)
{
return v___x_251_;
}
else
{
v_x_241_ = v_s_248_;
v_x_242_ = v_s_250_;
goto _start;
}
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqSeq_beq___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_Grind_AC_instBEqSeq_beq(v_x_254_, v_x_255_);
lean_dec_ref(v_x_255_);
lean_dec_ref(v_x_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter___redArg(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_, lean_object* v_h__3_264_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_dec(v_h__2_263_);
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_x_265_; lean_object* v_x_266_; lean_object* v___x_267_; 
lean_dec(v_h__3_264_);
v_x_265_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_x_265_);
lean_dec_ref_known(v_x_260_, 1);
v_x_266_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_x_266_);
lean_dec_ref_known(v_x_261_, 1);
v___x_267_ = lean_apply_2(v_h__1_262_, v_x_265_, v_x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
lean_dec(v_h__1_262_);
v___x_268_ = lean_apply_4(v_h__3_264_, v_x_260_, v_x_261_, lean_box(0), lean_box(0));
return v___x_268_;
}
}
else
{
lean_dec(v_h__1_262_);
if (lean_obj_tag(v_x_261_) == 1)
{
lean_object* v_x_269_; lean_object* v_s_270_; lean_object* v_x_271_; lean_object* v_s_272_; lean_object* v___x_273_; 
lean_dec(v_h__3_264_);
v_x_269_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_x_269_);
v_s_270_ = lean_ctor_get(v_x_260_, 1);
lean_inc_ref(v_s_270_);
lean_dec_ref_known(v_x_260_, 2);
v_x_271_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_x_271_);
v_s_272_ = lean_ctor_get(v_x_261_, 1);
lean_inc_ref(v_s_272_);
lean_dec_ref_known(v_x_261_, 2);
v___x_273_ = lean_apply_4(v_h__2_263_, v_x_269_, v_s_270_, v_x_271_, v_s_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v_h__2_263_);
v___x_274_ = lean_apply_4(v_h__3_264_, v_x_260_, v_x_261_, lean_box(0), lean_box(0));
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter(lean_object* v_motive_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_, lean_object* v_h__3_280_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec(v_h__2_279_);
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v_x_281_; lean_object* v_x_282_; lean_object* v___x_283_; 
lean_dec(v_h__3_280_);
v_x_281_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_x_281_);
lean_dec_ref_known(v_x_276_, 1);
v_x_282_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_x_282_);
lean_dec_ref_known(v_x_277_, 1);
v___x_283_ = lean_apply_2(v_h__1_278_, v_x_281_, v_x_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
lean_dec(v_h__1_278_);
v___x_284_ = lean_apply_4(v_h__3_280_, v_x_276_, v_x_277_, lean_box(0), lean_box(0));
return v___x_284_;
}
}
else
{
lean_dec(v_h__1_278_);
if (lean_obj_tag(v_x_277_) == 1)
{
lean_object* v_x_285_; lean_object* v_s_286_; lean_object* v_x_287_; lean_object* v_s_288_; lean_object* v___x_289_; 
lean_dec(v_h__3_280_);
v_x_285_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_x_285_);
v_s_286_ = lean_ctor_get(v_x_276_, 1);
lean_inc_ref(v_s_286_);
lean_dec_ref_known(v_x_276_, 2);
v_x_287_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_x_287_);
v_s_288_ = lean_ctor_get(v_x_277_, 1);
lean_inc_ref(v_s_288_);
lean_dec_ref_known(v_x_277_, 2);
v___x_289_ = lean_apply_4(v_h__2_279_, v_x_285_, v_s_286_, v_x_287_, v_s_288_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; 
lean_dec(v_h__2_279_);
v___x_290_ = lean_apply_4(v_h__3_280_, v_x_276_, v_x_277_, lean_box(0), lean_box(0));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27(lean_object* v_e_291_, lean_object* v_s_292_){
_start:
{
if (lean_obj_tag(v_e_291_) == 0)
{
lean_object* v_x_293_; lean_object* v___x_294_; 
v_x_293_ = lean_ctor_get(v_e_291_, 0);
lean_inc(v_x_293_);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v_x_293_);
lean_ctor_set(v___x_294_, 1, v_s_292_);
return v___x_294_;
}
else
{
lean_object* v_lhs_295_; lean_object* v_rhs_296_; lean_object* v___x_297_; 
v_lhs_295_ = lean_ctor_get(v_e_291_, 0);
v_rhs_296_ = lean_ctor_get(v_e_291_, 1);
v___x_297_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_rhs_296_, v_s_292_);
v_e_291_ = v_lhs_295_;
v_s_292_ = v___x_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27___boxed(lean_object* v_e_299_, lean_object* v_s_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_e_299_, v_s_300_);
lean_dec_ref(v_e_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter___redArg(lean_object* v_e_302_, lean_object* v_h__1_303_, lean_object* v_h__2_304_){
_start:
{
if (lean_obj_tag(v_e_302_) == 0)
{
lean_object* v_x_305_; lean_object* v___x_306_; 
lean_dec(v_h__2_304_);
v_x_305_ = lean_ctor_get(v_e_302_, 0);
lean_inc(v_x_305_);
lean_dec_ref_known(v_e_302_, 1);
v___x_306_ = lean_apply_1(v_h__1_303_, v_x_305_);
return v___x_306_;
}
else
{
lean_object* v_lhs_307_; lean_object* v_rhs_308_; lean_object* v___x_309_; 
lean_dec(v_h__1_303_);
v_lhs_307_ = lean_ctor_get(v_e_302_, 0);
lean_inc_ref(v_lhs_307_);
v_rhs_308_ = lean_ctor_get(v_e_302_, 1);
lean_inc_ref(v_rhs_308_);
lean_dec_ref_known(v_e_302_, 2);
v___x_309_ = lean_apply_2(v_h__2_304_, v_lhs_307_, v_rhs_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter(lean_object* v_motive_310_, lean_object* v_e_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
if (lean_obj_tag(v_e_311_) == 0)
{
lean_object* v_x_314_; lean_object* v___x_315_; 
lean_dec(v_h__2_313_);
v_x_314_ = lean_ctor_get(v_e_311_, 0);
lean_inc(v_x_314_);
lean_dec_ref_known(v_e_311_, 1);
v___x_315_ = lean_apply_1(v_h__1_312_, v_x_314_);
return v___x_315_;
}
else
{
lean_object* v_lhs_316_; lean_object* v_rhs_317_; lean_object* v___x_318_; 
lean_dec(v_h__1_312_);
v_lhs_316_ = lean_ctor_get(v_e_311_, 0);
lean_inc_ref(v_lhs_316_);
v_rhs_317_ = lean_ctor_get(v_e_311_, 1);
lean_inc_ref(v_rhs_317_);
lean_dec_ref_known(v_e_311_, 2);
v___x_318_ = lean_apply_2(v_h__2_313_, v_lhs_316_, v_rhs_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq(lean_object* v_e_319_){
_start:
{
if (lean_obj_tag(v_e_319_) == 0)
{
lean_object* v_x_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_x_320_ = lean_ctor_get(v_e_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_e_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v_e_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_x_320_);
lean_dec(v_e_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_x_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_lhs_328_; lean_object* v_rhs_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_lhs_328_ = lean_ctor_get(v_e_319_, 0);
lean_inc_ref(v_lhs_328_);
v_rhs_329_ = lean_ctor_get(v_e_319_, 1);
lean_inc_ref(v_rhs_329_);
lean_dec_ref_known(v_e_319_, 2);
v___x_330_ = l_Lean_Grind_AC_Expr_toSeq(v_rhs_329_);
v___x_331_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_lhs_328_, v___x_330_);
lean_dec_ref(v_lhs_328_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_erase0(lean_object* v_s_332_){
_start:
{
if (lean_obj_tag(v_s_332_) == 0)
{
return v_s_332_;
}
else
{
lean_object* v_x_333_; lean_object* v_s_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_347_; 
v_x_333_ = lean_ctor_get(v_s_332_, 0);
v_s_334_ = lean_ctor_get(v_s_332_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_s_332_);
if (v_isSharedCheck_347_ == 0)
{
v___x_336_ = v_s_332_;
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_s_334_);
lean_inc(v_x_333_);
lean_dec(v_s_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_s_x27_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_s_x27_338_ = l_Lean_Grind_AC_Seq_erase0(v_s_334_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v_x_333_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0));
v___x_342_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_x27_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_344_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_s_x27_338_);
v___x_344_ = v___x_336_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_x_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_s_x27_338_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec_ref(v_s_x27_338_);
lean_del_object(v___x_336_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_x_333_);
return v___x_346_;
}
}
else
{
lean_del_object(v___x_336_);
lean_dec(v_x_333_);
return v_s_x27_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(lean_object* v_s_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
if (lean_obj_tag(v_s_348_) == 0)
{
lean_object* v_x_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_350_);
v_x_351_ = lean_ctor_get(v_s_348_, 0);
lean_inc(v_x_351_);
lean_dec_ref_known(v_s_348_, 1);
v___x_352_ = lean_apply_1(v_h__1_349_, v_x_351_);
return v___x_352_;
}
else
{
lean_object* v_x_353_; lean_object* v_s_354_; lean_object* v___x_355_; 
lean_dec(v_h__1_349_);
v_x_353_ = lean_ctor_get(v_s_348_, 0);
lean_inc(v_x_353_);
v_s_354_ = lean_ctor_get(v_s_348_, 1);
lean_inc_ref(v_s_354_);
lean_dec_ref_known(v_s_348_, 2);
v___x_355_ = lean_apply_2(v_h__2_350_, v_x_353_, v_s_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter(lean_object* v_motive_356_, lean_object* v_s_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_){
_start:
{
if (lean_obj_tag(v_s_357_) == 0)
{
lean_object* v_x_360_; lean_object* v___x_361_; 
lean_dec(v_h__2_359_);
v_x_360_ = lean_ctor_get(v_s_357_, 0);
lean_inc(v_x_360_);
lean_dec_ref_known(v_s_357_, 1);
v___x_361_ = lean_apply_1(v_h__1_358_, v_x_360_);
return v___x_361_;
}
else
{
lean_object* v_x_362_; lean_object* v_s_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_358_);
v_x_362_ = lean_ctor_get(v_s_357_, 0);
lean_inc(v_x_362_);
v_s_363_ = lean_ctor_get(v_s_357_, 1);
lean_inc_ref(v_s_363_);
lean_dec_ref_known(v_s_357_, 2);
v___x_364_ = lean_apply_2(v_h__2_359_, v_x_362_, v_s_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_insert(lean_object* v_x_365_, lean_object* v_s_366_){
_start:
{
if (lean_obj_tag(v_s_366_) == 0)
{
lean_object* v_x_367_; uint8_t v___x_368_; 
v_x_367_ = lean_ctor_get(v_s_366_, 0);
v___x_368_ = l_Nat_blt(v_x_365_, v_x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
lean_inc(v_x_367_);
v_isSharedCheck_376_ = !lean_is_exclusive(v_s_366_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_s_366_, 0);
lean_dec(v_unused_377_);
v___x_370_ = v_s_366_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_dec(v_s_366_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_x_365_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_x_365_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v_x_367_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_x_365_);
lean_ctor_set(v___x_378_, 1, v_s_366_);
return v___x_378_;
}
}
else
{
lean_object* v_x_379_; lean_object* v_s_380_; uint8_t v___x_381_; 
v_x_379_ = lean_ctor_get(v_s_366_, 0);
v_s_380_ = lean_ctor_get(v_s_366_, 1);
v___x_381_ = l_Nat_blt(v_x_365_, v_x_379_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
lean_inc_ref(v_s_380_);
lean_inc(v_x_379_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_s_366_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; lean_object* v_unused_391_; 
v_unused_390_ = lean_ctor_get(v_s_366_, 1);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_s_366_, 0);
lean_dec(v_unused_391_);
v___x_383_ = v_s_366_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_s_366_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_Grind_AC_Seq_insert(v_x_365_, v_s_380_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_x_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_x_365_);
lean_ctor_set(v___x_392_, 1, v_s_366_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort_x27(lean_object* v_s_393_, lean_object* v_acc_394_){
_start:
{
if (lean_obj_tag(v_s_393_) == 0)
{
lean_object* v_x_395_; lean_object* v___x_396_; 
v_x_395_ = lean_ctor_get(v_s_393_, 0);
lean_inc(v_x_395_);
lean_dec_ref_known(v_s_393_, 1);
v___x_396_ = l_Lean_Grind_AC_Seq_insert(v_x_395_, v_acc_394_);
return v___x_396_;
}
else
{
lean_object* v_x_397_; lean_object* v_s_398_; lean_object* v___x_399_; 
v_x_397_ = lean_ctor_get(v_s_393_, 0);
lean_inc(v_x_397_);
v_s_398_ = lean_ctor_get(v_s_393_, 1);
lean_inc_ref(v_s_398_);
lean_dec_ref_known(v_s_393_, 2);
v___x_399_ = l_Lean_Grind_AC_Seq_insert(v_x_397_, v_acc_394_);
v_s_393_ = v_s_398_;
v_acc_394_ = v___x_399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort(lean_object* v_s_401_){
_start:
{
if (lean_obj_tag(v_s_401_) == 0)
{
return v_s_401_;
}
else
{
lean_object* v_x_402_; lean_object* v_s_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_x_402_ = lean_ctor_get(v_s_401_, 0);
lean_inc(v_x_402_);
v_s_403_ = lean_ctor_get(v_s_401_, 1);
lean_inc_ref(v_s_403_);
lean_dec_ref_known(v_s_401_, 2);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_x_402_);
v___x_405_ = l_Lean_Grind_AC_Seq_sort_x27(v_s_403_, v___x_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_eraseDup(lean_object* v_s_406_){
_start:
{
if (lean_obj_tag(v_s_406_) == 0)
{
return v_s_406_;
}
else
{
lean_object* v_x_407_; lean_object* v_s_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_431_; 
v_x_407_ = lean_ctor_get(v_s_406_, 0);
v_s_408_ = lean_ctor_get(v_s_406_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_s_406_);
if (v_isSharedCheck_431_ == 0)
{
v___x_410_ = v_s_406_;
v_isShared_411_ = v_isSharedCheck_431_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_s_408_);
lean_inc(v_x_407_);
lean_dec(v_s_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_431_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_s_x27_412_; 
v_s_x27_412_ = l_Lean_Grind_AC_Seq_eraseDup(v_s_408_);
if (lean_obj_tag(v_s_x27_412_) == 0)
{
lean_object* v_x_413_; uint8_t v___x_414_; 
v_x_413_ = lean_ctor_get(v_s_x27_412_, 0);
v___x_414_ = lean_nat_dec_eq(v_x_407_, v_x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_416_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_s_x27_412_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_x_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_s_x27_412_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_del_object(v___x_410_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_s_x27_412_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_s_x27_412_, 0);
lean_dec(v_unused_425_);
v___x_419_ = v_s_x27_412_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_s_x27_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_x_407_);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_x_407_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_x_426_; uint8_t v___x_427_; 
v_x_426_ = lean_ctor_get(v_s_x27_412_, 0);
v___x_427_ = lean_nat_dec_eq(v_x_407_, v_x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_429_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_s_x27_412_);
v___x_429_ = v___x_410_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_x_407_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_s_x27_412_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_del_object(v___x_410_);
lean_dec(v_x_407_);
return v_s_x27_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_concat(lean_object* v_s_u2081_432_, lean_object* v_s_u2082_433_){
_start:
{
if (lean_obj_tag(v_s_u2081_432_) == 0)
{
lean_object* v_x_434_; lean_object* v___x_435_; 
v_x_434_ = lean_ctor_get(v_s_u2081_432_, 0);
lean_inc(v_x_434_);
lean_dec_ref_known(v_s_u2081_432_, 1);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v_x_434_);
lean_ctor_set(v___x_435_, 1, v_s_u2082_433_);
return v___x_435_;
}
else
{
lean_object* v_x_436_; lean_object* v_s_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_x_436_ = lean_ctor_get(v_s_u2081_432_, 0);
v_s_437_ = lean_ctor_get(v_s_u2081_432_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_s_u2081_432_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v_s_u2081_432_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_s_437_);
lean_inc(v_x_436_);
lean_dec(v_s_u2081_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_Grind_AC_Seq_concat(v_s_437_, v_s_u2082_433_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_x_436_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel(lean_object* v_fuel_446_, lean_object* v_s_u2081_447_, lean_object* v_s_u2082_448_){
_start:
{
lean_object* v_zero_449_; uint8_t v_isZero_450_; 
v_zero_449_ = lean_unsigned_to_nat(0u);
v_isZero_450_ = lean_nat_dec_eq(v_fuel_446_, v_zero_449_);
if (v_isZero_450_ == 1)
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Grind_AC_Seq_concat(v_s_u2081_447_, v_s_u2082_448_);
return v___x_451_;
}
else
{
if (lean_obj_tag(v_s_u2081_447_) == 0)
{
if (lean_obj_tag(v_s_u2082_448_) == 0)
{
lean_object* v_x_452_; lean_object* v_x_453_; uint8_t v___x_454_; 
v_x_452_ = lean_ctor_get(v_s_u2081_447_, 0);
v_x_453_ = lean_ctor_get(v_s_u2082_448_, 0);
v___x_454_ = l_Nat_blt(v_x_452_, v_x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_inc(v_x_453_);
lean_dec_ref_known(v_s_u2082_448_, 1);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v_x_453_);
lean_ctor_set(v___x_455_, 1, v_s_u2081_447_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
lean_inc(v_x_452_);
lean_dec_ref_known(v_s_u2081_447_, 1);
v___x_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_456_, 0, v_x_452_);
lean_ctor_set(v___x_456_, 1, v_s_u2082_448_);
return v___x_456_;
}
}
else
{
lean_object* v_x_457_; lean_object* v___x_458_; 
v_x_457_ = lean_ctor_get(v_s_u2081_447_, 0);
lean_inc(v_x_457_);
lean_dec_ref_known(v_s_u2081_447_, 1);
v___x_458_ = l_Lean_Grind_AC_Seq_insert(v_x_457_, v_s_u2082_448_);
return v___x_458_;
}
}
else
{
if (lean_obj_tag(v_s_u2082_448_) == 0)
{
lean_object* v_x_459_; lean_object* v___x_460_; 
v_x_459_ = lean_ctor_get(v_s_u2082_448_, 0);
lean_inc(v_x_459_);
lean_dec_ref_known(v_s_u2082_448_, 1);
v___x_460_ = l_Lean_Grind_AC_Seq_insert(v_x_459_, v_s_u2081_447_);
return v___x_460_;
}
else
{
lean_object* v_x_461_; lean_object* v_s_462_; lean_object* v_x_463_; lean_object* v_s_464_; lean_object* v_one_465_; lean_object* v_n_466_; uint8_t v___x_467_; 
v_x_461_ = lean_ctor_get(v_s_u2081_447_, 0);
v_s_462_ = lean_ctor_get(v_s_u2081_447_, 1);
v_x_463_ = lean_ctor_get(v_s_u2082_448_, 0);
v_s_464_ = lean_ctor_get(v_s_u2082_448_, 1);
v_one_465_ = lean_unsigned_to_nat(1u);
v_n_466_ = lean_nat_sub(v_fuel_446_, v_one_465_);
v___x_467_ = l_Nat_blt(v_x_461_, v_x_463_);
if (v___x_467_ == 0)
{
lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
lean_inc_ref(v_s_464_);
lean_inc(v_x_463_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_u2082_448_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_476_ = lean_ctor_get(v_s_u2082_448_, 1);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_u2082_448_, 0);
lean_dec(v_unused_477_);
v___x_469_ = v_s_u2082_448_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_dec(v_s_u2082_448_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_466_, v_s_u2081_447_, v_s_464_);
lean_dec(v_n_466_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
lean_inc_ref(v_s_462_);
lean_inc(v_x_461_);
v_isSharedCheck_485_ = !lean_is_exclusive(v_s_u2081_447_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_s_u2081_447_, 1);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_s_u2081_447_, 0);
lean_dec(v_unused_487_);
v___x_479_ = v_s_u2081_447_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_dec(v_s_u2081_447_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_466_, v_s_462_, v_s_u2082_448_);
lean_dec(v_n_466_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_x_461_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel___boxed(lean_object* v_fuel_488_, lean_object* v_s_u2081_489_, lean_object* v_s_u2082_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Grind_AC_Seq_unionFuel(v_fuel_488_, v_s_u2081_489_, v_s_u2082_490_);
lean_dec(v_fuel_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(lean_object* v_fuel_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_){
_start:
{
lean_object* v_zero_495_; uint8_t v_isZero_496_; 
v_zero_495_ = lean_unsigned_to_nat(0u);
v_isZero_496_ = lean_nat_dec_eq(v_fuel_492_, v_zero_495_);
if (v_isZero_496_ == 1)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_h__2_494_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_apply_1(v_h__1_493_, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v_one_499_; lean_object* v_n_500_; lean_object* v___x_501_; 
lean_dec(v_h__1_493_);
v_one_499_ = lean_unsigned_to_nat(1u);
v_n_500_ = lean_nat_sub(v_fuel_492_, v_one_499_);
v___x_501_ = lean_apply_1(v_h__2_494_, v_n_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg___boxed(lean_object* v_fuel_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(v_fuel_502_, v_h__1_503_, v_h__2_504_);
lean_dec(v_fuel_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(lean_object* v_motive_506_, lean_object* v_fuel_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
lean_object* v_zero_510_; uint8_t v_isZero_511_; 
v_zero_510_ = lean_unsigned_to_nat(0u);
v_isZero_511_ = lean_nat_dec_eq(v_fuel_507_, v_zero_510_);
if (v_isZero_511_ == 1)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_509_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_h__1_508_, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v_one_514_; lean_object* v_n_515_; lean_object* v___x_516_; 
lean_dec(v_h__1_508_);
v_one_514_ = lean_unsigned_to_nat(1u);
v_n_515_ = lean_nat_sub(v_fuel_507_, v_one_514_);
v___x_516_ = lean_apply_1(v_h__2_509_, v_n_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___boxed(lean_object* v_motive_517_, lean_object* v_fuel_518_, lean_object* v_h__1_519_, lean_object* v_h__2_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(v_motive_517_, v_fuel_518_, v_h__1_519_, v_h__2_520_);
lean_dec(v_fuel_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(lean_object* v_s_u2081_522_, lean_object* v_s_u2082_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_, lean_object* v_h__3_526_, lean_object* v_h__4_527_){
_start:
{
if (lean_obj_tag(v_s_u2081_522_) == 0)
{
lean_dec(v_h__4_527_);
lean_dec(v_h__3_526_);
if (lean_obj_tag(v_s_u2082_523_) == 0)
{
lean_object* v_x_528_; lean_object* v_x_529_; lean_object* v___x_530_; 
lean_dec(v_h__2_525_);
v_x_528_ = lean_ctor_get(v_s_u2081_522_, 0);
lean_inc(v_x_528_);
lean_dec_ref_known(v_s_u2081_522_, 1);
v_x_529_ = lean_ctor_get(v_s_u2082_523_, 0);
lean_inc(v_x_529_);
lean_dec_ref_known(v_s_u2082_523_, 1);
v___x_530_ = lean_apply_2(v_h__1_524_, v_x_528_, v_x_529_);
return v___x_530_;
}
else
{
lean_object* v_x_531_; lean_object* v_x_532_; lean_object* v_s_533_; lean_object* v___x_534_; 
lean_dec(v_h__1_524_);
v_x_531_ = lean_ctor_get(v_s_u2081_522_, 0);
lean_inc(v_x_531_);
lean_dec_ref_known(v_s_u2081_522_, 1);
v_x_532_ = lean_ctor_get(v_s_u2082_523_, 0);
lean_inc(v_x_532_);
v_s_533_ = lean_ctor_get(v_s_u2082_523_, 1);
lean_inc_ref(v_s_533_);
lean_dec_ref_known(v_s_u2082_523_, 2);
v___x_534_ = lean_apply_3(v_h__2_525_, v_x_531_, v_x_532_, v_s_533_);
return v___x_534_;
}
}
else
{
lean_dec(v_h__2_525_);
lean_dec(v_h__1_524_);
if (lean_obj_tag(v_s_u2082_523_) == 0)
{
lean_object* v_x_535_; lean_object* v_s_536_; lean_object* v_x_537_; lean_object* v___x_538_; 
lean_dec(v_h__4_527_);
v_x_535_ = lean_ctor_get(v_s_u2081_522_, 0);
lean_inc(v_x_535_);
v_s_536_ = lean_ctor_get(v_s_u2081_522_, 1);
lean_inc_ref(v_s_536_);
lean_dec_ref_known(v_s_u2081_522_, 2);
v_x_537_ = lean_ctor_get(v_s_u2082_523_, 0);
lean_inc(v_x_537_);
lean_dec_ref_known(v_s_u2082_523_, 1);
v___x_538_ = lean_apply_3(v_h__3_526_, v_x_535_, v_s_536_, v_x_537_);
return v___x_538_;
}
else
{
lean_object* v_x_539_; lean_object* v_s_540_; lean_object* v_x_541_; lean_object* v_s_542_; lean_object* v___x_543_; 
lean_dec(v_h__3_526_);
v_x_539_ = lean_ctor_get(v_s_u2081_522_, 0);
lean_inc(v_x_539_);
v_s_540_ = lean_ctor_get(v_s_u2081_522_, 1);
lean_inc_ref(v_s_540_);
lean_dec_ref_known(v_s_u2081_522_, 2);
v_x_541_ = lean_ctor_get(v_s_u2082_523_, 0);
lean_inc(v_x_541_);
v_s_542_ = lean_ctor_get(v_s_u2082_523_, 1);
lean_inc_ref(v_s_542_);
lean_dec_ref_known(v_s_u2082_523_, 2);
v___x_543_ = lean_apply_4(v_h__4_527_, v_x_539_, v_s_540_, v_x_541_, v_s_542_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter(lean_object* v_motive_544_, lean_object* v_s_u2081_545_, lean_object* v_s_u2082_546_, lean_object* v_h__1_547_, lean_object* v_h__2_548_, lean_object* v_h__3_549_, lean_object* v_h__4_550_){
_start:
{
if (lean_obj_tag(v_s_u2081_545_) == 0)
{
lean_dec(v_h__4_550_);
lean_dec(v_h__3_549_);
if (lean_obj_tag(v_s_u2082_546_) == 0)
{
lean_object* v_x_551_; lean_object* v_x_552_; lean_object* v___x_553_; 
lean_dec(v_h__2_548_);
v_x_551_ = lean_ctor_get(v_s_u2081_545_, 0);
lean_inc(v_x_551_);
lean_dec_ref_known(v_s_u2081_545_, 1);
v_x_552_ = lean_ctor_get(v_s_u2082_546_, 0);
lean_inc(v_x_552_);
lean_dec_ref_known(v_s_u2082_546_, 1);
v___x_553_ = lean_apply_2(v_h__1_547_, v_x_551_, v_x_552_);
return v___x_553_;
}
else
{
lean_object* v_x_554_; lean_object* v_x_555_; lean_object* v_s_556_; lean_object* v___x_557_; 
lean_dec(v_h__1_547_);
v_x_554_ = lean_ctor_get(v_s_u2081_545_, 0);
lean_inc(v_x_554_);
lean_dec_ref_known(v_s_u2081_545_, 1);
v_x_555_ = lean_ctor_get(v_s_u2082_546_, 0);
lean_inc(v_x_555_);
v_s_556_ = lean_ctor_get(v_s_u2082_546_, 1);
lean_inc_ref(v_s_556_);
lean_dec_ref_known(v_s_u2082_546_, 2);
v___x_557_ = lean_apply_3(v_h__2_548_, v_x_554_, v_x_555_, v_s_556_);
return v___x_557_;
}
}
else
{
lean_dec(v_h__2_548_);
lean_dec(v_h__1_547_);
if (lean_obj_tag(v_s_u2082_546_) == 0)
{
lean_object* v_x_558_; lean_object* v_s_559_; lean_object* v_x_560_; lean_object* v___x_561_; 
lean_dec(v_h__4_550_);
v_x_558_ = lean_ctor_get(v_s_u2081_545_, 0);
lean_inc(v_x_558_);
v_s_559_ = lean_ctor_get(v_s_u2081_545_, 1);
lean_inc_ref(v_s_559_);
lean_dec_ref_known(v_s_u2081_545_, 2);
v_x_560_ = lean_ctor_get(v_s_u2082_546_, 0);
lean_inc(v_x_560_);
lean_dec_ref_known(v_s_u2082_546_, 1);
v___x_561_ = lean_apply_3(v_h__3_549_, v_x_558_, v_s_559_, v_x_560_);
return v___x_561_;
}
else
{
lean_object* v_x_562_; lean_object* v_s_563_; lean_object* v_x_564_; lean_object* v_s_565_; lean_object* v___x_566_; 
lean_dec(v_h__3_549_);
v_x_562_ = lean_ctor_get(v_s_u2081_545_, 0);
lean_inc(v_x_562_);
v_s_563_ = lean_ctor_get(v_s_u2081_545_, 1);
lean_inc_ref(v_s_563_);
lean_dec_ref_known(v_s_u2081_545_, 2);
v_x_564_ = lean_ctor_get(v_s_u2082_546_, 0);
lean_inc(v_x_564_);
v_s_565_ = lean_ctor_get(v_s_u2082_546_, 1);
lean_inc_ref(v_s_565_);
lean_dec_ref_known(v_s_u2082_546_, 2);
v___x_566_ = lean_apply_4(v_h__4_550_, v_x_562_, v_s_563_, v_x_564_, v_s_565_);
return v___x_566_;
}
}
}
}
static lean_object* _init_l_Lean_Grind_AC_hugeFuel(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_unsigned_to_nat(1000000u);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_union(lean_object* v_s_u2081_568_, lean_object* v_s_u2082_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1000000u);
v___x_571_ = l_Lean_Grind_AC_Seq_unionFuel(v___x_570_, v_s_u2081_568_, v_s_u2082_569_);
return v___x_571_;
}
}
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_AC_hugeFuel = _init_l_Lean_Grind_AC_hugeFuel();
lean_mark_persistent(l_Lean_Grind_AC_hugeFuel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_AC(builtin);
}
#ifdef __cplusplus
}
#endif
