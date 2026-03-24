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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Grind_AC_Expr_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Grind_AC_Expr_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim___redArg(lean_object* v_t_25_, lean_object* v_var_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_25_, v_var_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_var_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_var_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_29_, v_var_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim___redArg(lean_object* v_t_33_, lean_object* v_op_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_33_, v_op_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_op_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_op_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_37_, v_op_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(2u);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr(lean_object* v_x_61_, lean_object* v_prec_62_){
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
v___x_81_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_68_ = v___x_82_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Lean_Grind_AC_instReprExpr_repr___closed__2));
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
v___x_106_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_91_ = v___x_106_;
goto v___jp_90_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_92_ = lean_box(1);
v___x_93_ = ((lean_object*)(l_Lean_Grind_AC_instReprExpr_repr___closed__7));
v___x_94_ = l_Lean_Grind_AC_instReprExpr_repr(v_lhs_84_, v___x_89_);
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
v___x_98_ = l_Lean_Grind_AC_instReprExpr_repr(v_rhs_85_, v___x_89_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprExpr_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Grind_AC_instReprExpr_repr(v_x_109_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqExpr_beq(lean_object* v_x_114_, lean_object* v_x_115_){
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
v___x_124_ = l_Lean_Grind_AC_instBEqExpr_beq(v_lhs_120_, v_lhs_122_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqExpr_beq___boxed(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Grind_AC_instBEqExpr_beq(v_x_127_, v_x_128_);
lean_dec_ref(v_x_128_);
lean_dec_ref(v_x_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx(lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(0u);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(1u);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorIdx___boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Grind_AC_Seq_ctorIdx(v_x_136_);
lean_dec_ref(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___redArg(lean_object* v_t_138_, lean_object* v_k_139_){
_start:
{
if (lean_obj_tag(v_t_138_) == 0)
{
lean_object* v_x_140_; lean_object* v___x_141_; 
v_x_140_ = lean_ctor_get(v_t_138_, 0);
lean_inc(v_x_140_);
lean_dec_ref(v_t_138_);
v___x_141_ = lean_apply_1(v_k_139_, v_x_140_);
return v___x_141_;
}
else
{
lean_object* v_x_142_; lean_object* v_s_143_; lean_object* v___x_144_; 
v_x_142_ = lean_ctor_get(v_t_138_, 0);
lean_inc(v_x_142_);
v_s_143_ = lean_ctor_get(v_t_138_, 1);
lean_inc_ref(v_s_143_);
lean_dec_ref(v_t_138_);
v___x_144_ = lean_apply_2(v_k_139_, v_x_142_, v_s_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim(lean_object* v_motive_145_, lean_object* v_ctorIdx_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_k_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_147_, v_k_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_ctorElim___boxed(lean_object* v_motive_151_, lean_object* v_ctorIdx_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Grind_AC_Seq_ctorElim(v_motive_151_, v_ctorIdx_152_, v_t_153_, v_h_154_, v_k_155_);
lean_dec(v_ctorIdx_152_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim___redArg(lean_object* v_t_157_, lean_object* v_var_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_157_, v_var_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_var_elim(lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_var_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_161_, v_var_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim___redArg(lean_object* v_t_165_, lean_object* v_cons_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_165_, v_cons_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_cons_elim(lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_cons_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_169_, v_cons_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr(lean_object* v_x_189_, lean_object* v_prec_190_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v_x_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_211_; 
v_x_191_ = lean_ctor_get(v_x_189_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_211_ == 0)
{
v___x_193_ = v_x_189_;
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_x_191_);
lean_dec(v_x_189_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___y_196_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1024u);
v___x_208_ = lean_nat_dec_le(v___x_207_, v_prec_190_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_196_ = v___x_209_;
goto v___jp_195_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_196_ = v___x_210_;
goto v___jp_195_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_197_ = ((lean_object*)(l_Lean_Grind_AC_instReprSeq_repr___closed__2));
v___x_198_ = l_Nat_reprFast(v_x_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 3);
lean_ctor_set(v___x_193_, 0, v___x_198_);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_206_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_197_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___y_196_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = 0;
v___x_204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_prec_190_);
return v___x_205_;
}
}
}
}
else
{
lean_object* v_x_212_; lean_object* v_s_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_237_; 
v_x_212_ = lean_ctor_get(v_x_189_, 0);
v_s_213_ = lean_ctor_get(v_x_189_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_237_ == 0)
{
v___x_215_ = v_x_189_;
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_s_213_);
lean_inc(v_x_212_);
lean_dec(v_x_189_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___y_219_; uint8_t v___x_234_; 
v___x_217_ = lean_unsigned_to_nat(1024u);
v___x_234_ = lean_nat_dec_le(v___x_217_, v_prec_190_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__3, &l_Lean_Grind_AC_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3);
v___y_219_ = v___x_235_;
goto v___jp_218_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_Grind_AC_instReprExpr_repr___closed__4, &l_Lean_Grind_AC_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4);
v___y_219_ = v___x_236_;
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_220_ = lean_box(1);
v___x_221_ = ((lean_object*)(l_Lean_Grind_AC_instReprSeq_repr___closed__5));
v___x_222_ = l_Nat_reprFast(v_x_212_);
v___x_223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 5);
lean_ctor_set(v___x_215_, 1, v___x_223_);
lean_ctor_set(v___x_215_, 0, v___x_221_);
v___x_225_ = v___x_215_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_233_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_220_);
v___x_227_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_213_, v___x_217_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_219_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = l_Repr_addAppParen(v___x_231_, v_prec_190_);
return v___x_232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instReprSeq_repr___boxed(lean_object* v_x_238_, lean_object* v_prec_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Grind_AC_instReprSeq_repr(v_x_238_, v_prec_239_);
lean_dec(v_prec_239_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_x_245_; lean_object* v_x_246_; uint8_t v___x_247_; 
v_x_245_ = lean_ctor_get(v_x_243_, 0);
v_x_246_ = lean_ctor_get(v_x_244_, 0);
v___x_247_ = lean_nat_dec_eq(v_x_245_, v_x_246_);
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
}
else
{
if (lean_obj_tag(v_x_244_) == 1)
{
lean_object* v_x_249_; lean_object* v_s_250_; lean_object* v_x_251_; lean_object* v_s_252_; uint8_t v___x_253_; 
v_x_249_ = lean_ctor_get(v_x_243_, 0);
v_s_250_ = lean_ctor_get(v_x_243_, 1);
v_x_251_ = lean_ctor_get(v_x_244_, 0);
v_s_252_ = lean_ctor_get(v_x_244_, 1);
v___x_253_ = lean_nat_dec_eq(v_x_249_, v_x_251_);
if (v___x_253_ == 0)
{
return v___x_253_;
}
else
{
v_x_243_ = v_s_250_;
v_x_244_ = v_s_252_;
goto _start;
}
}
else
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instBEqSeq_beq___boxed(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Lean_Grind_AC_instBEqSeq_beq(v_x_256_, v_x_257_);
lean_dec_ref(v_x_257_);
lean_dec_ref(v_x_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter___redArg(lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_, lean_object* v_h__3_266_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_dec(v_h__2_265_);
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_x_267_; lean_object* v_x_268_; lean_object* v___x_269_; 
lean_dec(v_h__3_266_);
v_x_267_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_x_267_);
lean_dec_ref(v_x_262_);
v_x_268_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_x_268_);
lean_dec_ref(v_x_263_);
v___x_269_ = lean_apply_2(v_h__1_264_, v_x_267_, v_x_268_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v_h__1_264_);
v___x_270_ = lean_apply_4(v_h__3_266_, v_x_262_, v_x_263_, lean_box(0), lean_box(0));
return v___x_270_;
}
}
else
{
lean_dec(v_h__1_264_);
if (lean_obj_tag(v_x_263_) == 1)
{
lean_object* v_x_271_; lean_object* v_s_272_; lean_object* v_x_273_; lean_object* v_s_274_; lean_object* v___x_275_; 
lean_dec(v_h__3_266_);
v_x_271_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_x_271_);
v_s_272_ = lean_ctor_get(v_x_262_, 1);
lean_inc_ref(v_s_272_);
lean_dec_ref(v_x_262_);
v_x_273_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_x_273_);
v_s_274_ = lean_ctor_get(v_x_263_, 1);
lean_inc_ref(v_s_274_);
lean_dec_ref(v_x_263_);
v___x_275_ = lean_apply_4(v_h__2_265_, v_x_271_, v_s_272_, v_x_273_, v_s_274_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; 
lean_dec(v_h__2_265_);
v___x_276_ = lean_apply_4(v_h__3_266_, v_x_262_, v_x_263_, lean_box(0), lean_box(0));
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter(lean_object* v_motive_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_, lean_object* v_h__3_282_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_dec(v_h__2_281_);
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_x_283_; lean_object* v_x_284_; lean_object* v___x_285_; 
lean_dec(v_h__3_282_);
v_x_283_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_x_283_);
lean_dec_ref(v_x_278_);
v_x_284_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_x_284_);
lean_dec_ref(v_x_279_);
v___x_285_ = lean_apply_2(v_h__1_280_, v_x_283_, v_x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; 
lean_dec(v_h__1_280_);
v___x_286_ = lean_apply_4(v_h__3_282_, v_x_278_, v_x_279_, lean_box(0), lean_box(0));
return v___x_286_;
}
}
else
{
lean_dec(v_h__1_280_);
if (lean_obj_tag(v_x_279_) == 1)
{
lean_object* v_x_287_; lean_object* v_s_288_; lean_object* v_x_289_; lean_object* v_s_290_; lean_object* v___x_291_; 
lean_dec(v_h__3_282_);
v_x_287_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_x_287_);
v_s_288_ = lean_ctor_get(v_x_278_, 1);
lean_inc_ref(v_s_288_);
lean_dec_ref(v_x_278_);
v_x_289_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_x_289_);
v_s_290_ = lean_ctor_get(v_x_279_, 1);
lean_inc_ref(v_s_290_);
lean_dec_ref(v_x_279_);
v___x_291_ = lean_apply_4(v_h__2_281_, v_x_287_, v_s_288_, v_x_289_, v_s_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_dec(v_h__2_281_);
v___x_292_ = lean_apply_4(v_h__3_282_, v_x_278_, v_x_279_, lean_box(0), lean_box(0));
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27(lean_object* v_e_293_, lean_object* v_s_294_){
_start:
{
if (lean_obj_tag(v_e_293_) == 0)
{
lean_object* v_x_295_; lean_object* v___x_296_; 
v_x_295_ = lean_ctor_get(v_e_293_, 0);
lean_inc(v_x_295_);
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v_x_295_);
lean_ctor_set(v___x_296_, 1, v_s_294_);
return v___x_296_;
}
else
{
lean_object* v_lhs_297_; lean_object* v_rhs_298_; lean_object* v___x_299_; 
v_lhs_297_ = lean_ctor_get(v_e_293_, 0);
v_rhs_298_ = lean_ctor_get(v_e_293_, 1);
v___x_299_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_rhs_298_, v_s_294_);
v_e_293_ = v_lhs_297_;
v_s_294_ = v___x_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq_x27___boxed(lean_object* v_e_301_, lean_object* v_s_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_e_301_, v_s_302_);
lean_dec_ref(v_e_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter___redArg(lean_object* v_e_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
if (lean_obj_tag(v_e_304_) == 0)
{
lean_object* v_x_307_; lean_object* v___x_308_; 
lean_dec(v_h__2_306_);
v_x_307_ = lean_ctor_get(v_e_304_, 0);
lean_inc(v_x_307_);
lean_dec_ref(v_e_304_);
v___x_308_ = lean_apply_1(v_h__1_305_, v_x_307_);
return v___x_308_;
}
else
{
lean_object* v_lhs_309_; lean_object* v_rhs_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_305_);
v_lhs_309_ = lean_ctor_get(v_e_304_, 0);
lean_inc_ref(v_lhs_309_);
v_rhs_310_ = lean_ctor_get(v_e_304_, 1);
lean_inc_ref(v_rhs_310_);
lean_dec_ref(v_e_304_);
v___x_311_ = lean_apply_2(v_h__2_306_, v_lhs_309_, v_rhs_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter(lean_object* v_motive_312_, lean_object* v_e_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_e_313_) == 0)
{
lean_object* v_x_316_; lean_object* v___x_317_; 
lean_dec(v_h__2_315_);
v_x_316_ = lean_ctor_get(v_e_313_, 0);
lean_inc(v_x_316_);
lean_dec_ref(v_e_313_);
v___x_317_ = lean_apply_1(v_h__1_314_, v_x_316_);
return v___x_317_;
}
else
{
lean_object* v_lhs_318_; lean_object* v_rhs_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_314_);
v_lhs_318_ = lean_ctor_get(v_e_313_, 0);
lean_inc_ref(v_lhs_318_);
v_rhs_319_ = lean_ctor_get(v_e_313_, 1);
lean_inc_ref(v_rhs_319_);
lean_dec_ref(v_e_313_);
v___x_320_ = lean_apply_2(v_h__2_315_, v_lhs_318_, v_rhs_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq(lean_object* v_e_321_){
_start:
{
if (lean_obj_tag(v_e_321_) == 0)
{
lean_object* v_x_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_x_322_ = lean_ctor_get(v_e_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_e_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v_e_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_x_322_);
lean_dec(v_e_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_x_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_lhs_330_; lean_object* v_rhs_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_lhs_330_ = lean_ctor_get(v_e_321_, 0);
lean_inc_ref(v_lhs_330_);
v_rhs_331_ = lean_ctor_get(v_e_321_, 1);
lean_inc_ref(v_rhs_331_);
lean_dec_ref(v_e_321_);
v___x_332_ = l_Lean_Grind_AC_Expr_toSeq(v_rhs_331_);
v___x_333_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_lhs_330_, v___x_332_);
lean_dec_ref(v_lhs_330_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_erase0(lean_object* v_s_334_){
_start:
{
if (lean_obj_tag(v_s_334_) == 0)
{
return v_s_334_;
}
else
{
lean_object* v_x_335_; lean_object* v_s_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_349_; 
v_x_335_ = lean_ctor_get(v_s_334_, 0);
v_s_336_ = lean_ctor_get(v_s_334_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_s_334_);
if (v_isSharedCheck_349_ == 0)
{
v___x_338_ = v_s_334_;
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_s_336_);
lean_inc(v_x_335_);
lean_dec(v_s_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_s_x27_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_s_x27_340_ = l_Lean_Grind_AC_Seq_erase0(v_s_336_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_nat_dec_eq(v_x_335_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0));
v___x_344_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_x27_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v_s_x27_340_);
v___x_346_ = v___x_338_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_x_335_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_s_x27_340_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v___x_348_; 
lean_dec_ref(v_s_x27_340_);
lean_del_object(v___x_338_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_x_335_);
return v___x_348_;
}
}
else
{
lean_del_object(v___x_338_);
lean_dec(v_x_335_);
return v_s_x27_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(lean_object* v_s_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_){
_start:
{
if (lean_obj_tag(v_s_350_) == 0)
{
lean_object* v_x_353_; lean_object* v___x_354_; 
lean_dec(v_h__2_352_);
v_x_353_ = lean_ctor_get(v_s_350_, 0);
lean_inc(v_x_353_);
lean_dec_ref(v_s_350_);
v___x_354_ = lean_apply_1(v_h__1_351_, v_x_353_);
return v___x_354_;
}
else
{
lean_object* v_x_355_; lean_object* v_s_356_; lean_object* v___x_357_; 
lean_dec(v_h__1_351_);
v_x_355_ = lean_ctor_get(v_s_350_, 0);
lean_inc(v_x_355_);
v_s_356_ = lean_ctor_get(v_s_350_, 1);
lean_inc_ref(v_s_356_);
lean_dec_ref(v_s_350_);
v___x_357_ = lean_apply_2(v_h__2_352_, v_x_355_, v_s_356_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter(lean_object* v_motive_358_, lean_object* v_s_359_, lean_object* v_h__1_360_, lean_object* v_h__2_361_){
_start:
{
if (lean_obj_tag(v_s_359_) == 0)
{
lean_object* v_x_362_; lean_object* v___x_363_; 
lean_dec(v_h__2_361_);
v_x_362_ = lean_ctor_get(v_s_359_, 0);
lean_inc(v_x_362_);
lean_dec_ref(v_s_359_);
v___x_363_ = lean_apply_1(v_h__1_360_, v_x_362_);
return v___x_363_;
}
else
{
lean_object* v_x_364_; lean_object* v_s_365_; lean_object* v___x_366_; 
lean_dec(v_h__1_360_);
v_x_364_ = lean_ctor_get(v_s_359_, 0);
lean_inc(v_x_364_);
v_s_365_ = lean_ctor_get(v_s_359_, 1);
lean_inc_ref(v_s_365_);
lean_dec_ref(v_s_359_);
v___x_366_ = lean_apply_2(v_h__2_361_, v_x_364_, v_s_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_insert(lean_object* v_x_367_, lean_object* v_s_368_){
_start:
{
if (lean_obj_tag(v_s_368_) == 0)
{
lean_object* v_x_369_; uint8_t v___x_370_; 
v_x_369_ = lean_ctor_get(v_s_368_, 0);
v___x_370_ = l_Nat_blt(v_x_367_, v_x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
lean_inc(v_x_369_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_s_368_, 0);
lean_dec(v_unused_379_);
v___x_372_ = v_s_368_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_dec(v_s_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_x_367_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_x_367_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v_x_369_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
}
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v_x_367_);
lean_ctor_set(v___x_380_, 1, v_s_368_);
return v___x_380_;
}
}
else
{
lean_object* v_x_381_; lean_object* v_s_382_; uint8_t v___x_383_; 
v_x_381_ = lean_ctor_get(v_s_368_, 0);
v_s_382_ = lean_ctor_get(v_s_368_, 1);
v___x_383_ = l_Nat_blt(v_x_367_, v_x_381_);
if (v___x_383_ == 0)
{
lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
lean_inc_ref(v_s_382_);
lean_inc(v_x_381_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; lean_object* v_unused_393_; 
v_unused_392_ = lean_ctor_get(v_s_368_, 1);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_s_368_, 0);
lean_dec(v_unused_393_);
v___x_385_ = v_s_368_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_dec(v_s_368_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = l_Lean_Grind_AC_Seq_insert(v_x_367_, v_s_382_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v___x_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_x_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v_x_367_);
lean_ctor_set(v___x_394_, 1, v_s_368_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort_x27(lean_object* v_s_395_, lean_object* v_acc_396_){
_start:
{
if (lean_obj_tag(v_s_395_) == 0)
{
lean_object* v_x_397_; lean_object* v___x_398_; 
v_x_397_ = lean_ctor_get(v_s_395_, 0);
lean_inc(v_x_397_);
lean_dec_ref(v_s_395_);
v___x_398_ = l_Lean_Grind_AC_Seq_insert(v_x_397_, v_acc_396_);
return v___x_398_;
}
else
{
lean_object* v_x_399_; lean_object* v_s_400_; lean_object* v___x_401_; 
v_x_399_ = lean_ctor_get(v_s_395_, 0);
lean_inc(v_x_399_);
v_s_400_ = lean_ctor_get(v_s_395_, 1);
lean_inc_ref(v_s_400_);
lean_dec_ref(v_s_395_);
v___x_401_ = l_Lean_Grind_AC_Seq_insert(v_x_399_, v_acc_396_);
v_s_395_ = v_s_400_;
v_acc_396_ = v___x_401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort(lean_object* v_s_403_){
_start:
{
if (lean_obj_tag(v_s_403_) == 0)
{
return v_s_403_;
}
else
{
lean_object* v_x_404_; lean_object* v_s_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_x_404_ = lean_ctor_get(v_s_403_, 0);
lean_inc(v_x_404_);
v_s_405_ = lean_ctor_get(v_s_403_, 1);
lean_inc_ref(v_s_405_);
lean_dec_ref(v_s_403_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_x_404_);
v___x_407_ = l_Lean_Grind_AC_Seq_sort_x27(v_s_405_, v___x_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_eraseDup(lean_object* v_s_408_){
_start:
{
if (lean_obj_tag(v_s_408_) == 0)
{
return v_s_408_;
}
else
{
lean_object* v_x_409_; lean_object* v_s_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_433_; 
v_x_409_ = lean_ctor_get(v_s_408_, 0);
v_s_410_ = lean_ctor_get(v_s_408_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_s_408_);
if (v_isSharedCheck_433_ == 0)
{
v___x_412_ = v_s_408_;
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_s_410_);
lean_inc(v_x_409_);
lean_dec(v_s_408_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_s_x27_414_; 
v_s_x27_414_ = l_Lean_Grind_AC_Seq_eraseDup(v_s_410_);
if (lean_obj_tag(v_s_x27_414_) == 0)
{
lean_object* v_x_415_; uint8_t v___x_416_; 
v_x_415_ = lean_ctor_get(v_s_x27_414_, 0);
lean_inc(v_x_415_);
v___x_416_ = lean_nat_dec_eq(v_x_409_, v_x_415_);
lean_dec(v_x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_418_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_s_x27_414_);
v___x_418_ = v___x_412_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_x_409_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_s_x27_414_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_del_object(v___x_412_);
v_isSharedCheck_426_ = !lean_is_exclusive(v_s_x27_414_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_s_x27_414_, 0);
lean_dec(v_unused_427_);
v___x_421_ = v_s_x27_414_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_dec(v_s_x27_414_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_x_409_);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_x_409_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_x_428_; uint8_t v___x_429_; 
v_x_428_ = lean_ctor_get(v_s_x27_414_, 0);
lean_inc(v_x_428_);
v___x_429_ = lean_nat_dec_eq(v_x_409_, v_x_428_);
lean_dec(v_x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_s_x27_414_);
v___x_431_ = v___x_412_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_x_409_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_s_x27_414_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_del_object(v___x_412_);
lean_dec(v_x_409_);
return v_s_x27_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_concat(lean_object* v_s_u2081_434_, lean_object* v_s_u2082_435_){
_start:
{
if (lean_obj_tag(v_s_u2081_434_) == 0)
{
lean_object* v_x_436_; lean_object* v___x_437_; 
v_x_436_ = lean_ctor_get(v_s_u2081_434_, 0);
lean_inc(v_x_436_);
lean_dec_ref(v_s_u2081_434_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v_x_436_);
lean_ctor_set(v___x_437_, 1, v_s_u2082_435_);
return v___x_437_;
}
else
{
lean_object* v_x_438_; lean_object* v_s_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
v_x_438_ = lean_ctor_get(v_s_u2081_434_, 0);
v_s_439_ = lean_ctor_get(v_s_u2081_434_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_s_u2081_434_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v_s_u2081_434_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_s_439_);
lean_inc(v_x_438_);
lean_dec(v_s_u2081_434_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = l_Lean_Grind_AC_Seq_concat(v_s_439_, v_s_u2082_435_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_x_438_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel(lean_object* v_fuel_448_, lean_object* v_s_u2081_449_, lean_object* v_s_u2082_450_){
_start:
{
lean_object* v_zero_451_; uint8_t v_isZero_452_; 
v_zero_451_ = lean_unsigned_to_nat(0u);
v_isZero_452_ = lean_nat_dec_eq(v_fuel_448_, v_zero_451_);
if (v_isZero_452_ == 1)
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Grind_AC_Seq_concat(v_s_u2081_449_, v_s_u2082_450_);
return v___x_453_;
}
else
{
if (lean_obj_tag(v_s_u2081_449_) == 0)
{
if (lean_obj_tag(v_s_u2082_450_) == 0)
{
lean_object* v_x_454_; lean_object* v_x_455_; uint8_t v___x_456_; 
v_x_454_ = lean_ctor_get(v_s_u2081_449_, 0);
v_x_455_ = lean_ctor_get(v_s_u2082_450_, 0);
v___x_456_ = l_Nat_blt(v_x_454_, v_x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_inc(v_x_455_);
lean_dec_ref(v_s_u2082_450_);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v_x_455_);
lean_ctor_set(v___x_457_, 1, v_s_u2081_449_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
lean_inc(v_x_454_);
lean_dec_ref(v_s_u2081_449_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v_x_454_);
lean_ctor_set(v___x_458_, 1, v_s_u2082_450_);
return v___x_458_;
}
}
else
{
lean_object* v_x_459_; lean_object* v___x_460_; 
v_x_459_ = lean_ctor_get(v_s_u2081_449_, 0);
lean_inc(v_x_459_);
lean_dec_ref(v_s_u2081_449_);
v___x_460_ = l_Lean_Grind_AC_Seq_insert(v_x_459_, v_s_u2082_450_);
return v___x_460_;
}
}
else
{
if (lean_obj_tag(v_s_u2082_450_) == 0)
{
lean_object* v_x_461_; lean_object* v___x_462_; 
v_x_461_ = lean_ctor_get(v_s_u2082_450_, 0);
lean_inc(v_x_461_);
lean_dec_ref(v_s_u2082_450_);
v___x_462_ = l_Lean_Grind_AC_Seq_insert(v_x_461_, v_s_u2081_449_);
return v___x_462_;
}
else
{
lean_object* v_x_463_; lean_object* v_s_464_; lean_object* v_x_465_; lean_object* v_s_466_; lean_object* v_one_467_; lean_object* v_n_468_; uint8_t v___x_469_; 
v_x_463_ = lean_ctor_get(v_s_u2081_449_, 0);
v_s_464_ = lean_ctor_get(v_s_u2081_449_, 1);
v_x_465_ = lean_ctor_get(v_s_u2082_450_, 0);
v_s_466_ = lean_ctor_get(v_s_u2082_450_, 1);
v_one_467_ = lean_unsigned_to_nat(1u);
v_n_468_ = lean_nat_sub(v_fuel_448_, v_one_467_);
v___x_469_ = l_Nat_blt(v_x_463_, v_x_465_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_477_; 
lean_inc_ref(v_s_466_);
lean_inc(v_x_465_);
v_isSharedCheck_477_ = !lean_is_exclusive(v_s_u2082_450_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_478_ = lean_ctor_get(v_s_u2082_450_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_s_u2082_450_, 0);
lean_dec(v_unused_479_);
v___x_471_ = v_s_u2082_450_;
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_s_u2082_450_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_468_, v_s_u2081_449_, v_s_466_);
lean_dec(v_n_468_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_x_465_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
lean_inc_ref(v_s_464_);
lean_inc(v_x_463_);
v_isSharedCheck_487_ = !lean_is_exclusive(v_s_u2081_449_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; 
v_unused_488_ = lean_ctor_get(v_s_u2081_449_, 1);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_s_u2081_449_, 0);
lean_dec(v_unused_489_);
v___x_481_ = v_s_u2081_449_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_dec(v_s_u2081_449_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_468_, v_s_464_, v_s_u2082_450_);
lean_dec(v_n_468_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel___boxed(lean_object* v_fuel_490_, lean_object* v_s_u2081_491_, lean_object* v_s_u2082_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Grind_AC_Seq_unionFuel(v_fuel_490_, v_s_u2081_491_, v_s_u2082_492_);
lean_dec(v_fuel_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(lean_object* v_fuel_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
lean_object* v_zero_497_; uint8_t v_isZero_498_; 
v_zero_497_ = lean_unsigned_to_nat(0u);
v_isZero_498_ = lean_nat_dec_eq(v_fuel_494_, v_zero_497_);
if (v_isZero_498_ == 1)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_h__2_496_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_apply_1(v_h__1_495_, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v_one_501_; lean_object* v_n_502_; lean_object* v___x_503_; 
lean_dec(v_h__1_495_);
v_one_501_ = lean_unsigned_to_nat(1u);
v_n_502_ = lean_nat_sub(v_fuel_494_, v_one_501_);
v___x_503_ = lean_apply_1(v_h__2_496_, v_n_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg___boxed(lean_object* v_fuel_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(v_fuel_504_, v_h__1_505_, v_h__2_506_);
lean_dec(v_fuel_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(lean_object* v_motive_508_, lean_object* v_fuel_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_){
_start:
{
lean_object* v_zero_512_; uint8_t v_isZero_513_; 
v_zero_512_ = lean_unsigned_to_nat(0u);
v_isZero_513_ = lean_nat_dec_eq(v_fuel_509_, v_zero_512_);
if (v_isZero_513_ == 1)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_h__2_511_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_1(v_h__1_510_, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_one_516_; lean_object* v_n_517_; lean_object* v___x_518_; 
lean_dec(v_h__1_510_);
v_one_516_ = lean_unsigned_to_nat(1u);
v_n_517_ = lean_nat_sub(v_fuel_509_, v_one_516_);
v___x_518_ = lean_apply_1(v_h__2_511_, v_n_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___boxed(lean_object* v_motive_519_, lean_object* v_fuel_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(v_motive_519_, v_fuel_520_, v_h__1_521_, v_h__2_522_);
lean_dec(v_fuel_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(lean_object* v_s_u2081_524_, lean_object* v_s_u2082_525_, lean_object* v_h__1_526_, lean_object* v_h__2_527_, lean_object* v_h__3_528_, lean_object* v_h__4_529_){
_start:
{
if (lean_obj_tag(v_s_u2081_524_) == 0)
{
lean_dec(v_h__4_529_);
lean_dec(v_h__3_528_);
if (lean_obj_tag(v_s_u2082_525_) == 0)
{
lean_object* v_x_530_; lean_object* v_x_531_; lean_object* v___x_532_; 
lean_dec(v_h__2_527_);
v_x_530_ = lean_ctor_get(v_s_u2081_524_, 0);
lean_inc(v_x_530_);
lean_dec_ref(v_s_u2081_524_);
v_x_531_ = lean_ctor_get(v_s_u2082_525_, 0);
lean_inc(v_x_531_);
lean_dec_ref(v_s_u2082_525_);
v___x_532_ = lean_apply_2(v_h__1_526_, v_x_530_, v_x_531_);
return v___x_532_;
}
else
{
lean_object* v_x_533_; lean_object* v_x_534_; lean_object* v_s_535_; lean_object* v___x_536_; 
lean_dec(v_h__1_526_);
v_x_533_ = lean_ctor_get(v_s_u2081_524_, 0);
lean_inc(v_x_533_);
lean_dec_ref(v_s_u2081_524_);
v_x_534_ = lean_ctor_get(v_s_u2082_525_, 0);
lean_inc(v_x_534_);
v_s_535_ = lean_ctor_get(v_s_u2082_525_, 1);
lean_inc_ref(v_s_535_);
lean_dec_ref(v_s_u2082_525_);
v___x_536_ = lean_apply_3(v_h__2_527_, v_x_533_, v_x_534_, v_s_535_);
return v___x_536_;
}
}
else
{
lean_dec(v_h__2_527_);
lean_dec(v_h__1_526_);
if (lean_obj_tag(v_s_u2082_525_) == 0)
{
lean_object* v_x_537_; lean_object* v_s_538_; lean_object* v_x_539_; lean_object* v___x_540_; 
lean_dec(v_h__4_529_);
v_x_537_ = lean_ctor_get(v_s_u2081_524_, 0);
lean_inc(v_x_537_);
v_s_538_ = lean_ctor_get(v_s_u2081_524_, 1);
lean_inc_ref(v_s_538_);
lean_dec_ref(v_s_u2081_524_);
v_x_539_ = lean_ctor_get(v_s_u2082_525_, 0);
lean_inc(v_x_539_);
lean_dec_ref(v_s_u2082_525_);
v___x_540_ = lean_apply_3(v_h__3_528_, v_x_537_, v_s_538_, v_x_539_);
return v___x_540_;
}
else
{
lean_object* v_x_541_; lean_object* v_s_542_; lean_object* v_x_543_; lean_object* v_s_544_; lean_object* v___x_545_; 
lean_dec(v_h__3_528_);
v_x_541_ = lean_ctor_get(v_s_u2081_524_, 0);
lean_inc(v_x_541_);
v_s_542_ = lean_ctor_get(v_s_u2081_524_, 1);
lean_inc_ref(v_s_542_);
lean_dec_ref(v_s_u2081_524_);
v_x_543_ = lean_ctor_get(v_s_u2082_525_, 0);
lean_inc(v_x_543_);
v_s_544_ = lean_ctor_get(v_s_u2082_525_, 1);
lean_inc_ref(v_s_544_);
lean_dec_ref(v_s_u2082_525_);
v___x_545_ = lean_apply_4(v_h__4_529_, v_x_541_, v_s_542_, v_x_543_, v_s_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter(lean_object* v_motive_546_, lean_object* v_s_u2081_547_, lean_object* v_s_u2082_548_, lean_object* v_h__1_549_, lean_object* v_h__2_550_, lean_object* v_h__3_551_, lean_object* v_h__4_552_){
_start:
{
if (lean_obj_tag(v_s_u2081_547_) == 0)
{
lean_dec(v_h__4_552_);
lean_dec(v_h__3_551_);
if (lean_obj_tag(v_s_u2082_548_) == 0)
{
lean_object* v_x_553_; lean_object* v_x_554_; lean_object* v___x_555_; 
lean_dec(v_h__2_550_);
v_x_553_ = lean_ctor_get(v_s_u2081_547_, 0);
lean_inc(v_x_553_);
lean_dec_ref(v_s_u2081_547_);
v_x_554_ = lean_ctor_get(v_s_u2082_548_, 0);
lean_inc(v_x_554_);
lean_dec_ref(v_s_u2082_548_);
v___x_555_ = lean_apply_2(v_h__1_549_, v_x_553_, v_x_554_);
return v___x_555_;
}
else
{
lean_object* v_x_556_; lean_object* v_x_557_; lean_object* v_s_558_; lean_object* v___x_559_; 
lean_dec(v_h__1_549_);
v_x_556_ = lean_ctor_get(v_s_u2081_547_, 0);
lean_inc(v_x_556_);
lean_dec_ref(v_s_u2081_547_);
v_x_557_ = lean_ctor_get(v_s_u2082_548_, 0);
lean_inc(v_x_557_);
v_s_558_ = lean_ctor_get(v_s_u2082_548_, 1);
lean_inc_ref(v_s_558_);
lean_dec_ref(v_s_u2082_548_);
v___x_559_ = lean_apply_3(v_h__2_550_, v_x_556_, v_x_557_, v_s_558_);
return v___x_559_;
}
}
else
{
lean_dec(v_h__2_550_);
lean_dec(v_h__1_549_);
if (lean_obj_tag(v_s_u2082_548_) == 0)
{
lean_object* v_x_560_; lean_object* v_s_561_; lean_object* v_x_562_; lean_object* v___x_563_; 
lean_dec(v_h__4_552_);
v_x_560_ = lean_ctor_get(v_s_u2081_547_, 0);
lean_inc(v_x_560_);
v_s_561_ = lean_ctor_get(v_s_u2081_547_, 1);
lean_inc_ref(v_s_561_);
lean_dec_ref(v_s_u2081_547_);
v_x_562_ = lean_ctor_get(v_s_u2082_548_, 0);
lean_inc(v_x_562_);
lean_dec_ref(v_s_u2082_548_);
v___x_563_ = lean_apply_3(v_h__3_551_, v_x_560_, v_s_561_, v_x_562_);
return v___x_563_;
}
else
{
lean_object* v_x_564_; lean_object* v_s_565_; lean_object* v_x_566_; lean_object* v_s_567_; lean_object* v___x_568_; 
lean_dec(v_h__3_551_);
v_x_564_ = lean_ctor_get(v_s_u2081_547_, 0);
lean_inc(v_x_564_);
v_s_565_ = lean_ctor_get(v_s_u2081_547_, 1);
lean_inc_ref(v_s_565_);
lean_dec_ref(v_s_u2081_547_);
v_x_566_ = lean_ctor_get(v_s_u2082_548_, 0);
lean_inc(v_x_566_);
v_s_567_ = lean_ctor_get(v_s_u2082_548_, 1);
lean_inc_ref(v_s_567_);
lean_dec_ref(v_s_u2082_548_);
v___x_568_ = lean_apply_4(v_h__4_552_, v_x_564_, v_s_565_, v_x_566_, v_s_567_);
return v___x_568_;
}
}
}
}
static lean_object* _init_l_Lean_Grind_AC_hugeFuel(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(1000000u);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_union(lean_object* v_s_u2081_570_, lean_object* v_s_u2082_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1000000u);
v___x_573_ = l_Lean_Grind_AC_Seq_unionFuel(v___x_572_, v_s_u2081_570_, v_s_u2082_571_);
return v___x_573_;
}
}
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
