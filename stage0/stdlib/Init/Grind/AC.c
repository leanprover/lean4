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
lean_object* v___x_316_; 
v___x_316_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter___redArg(v_e_313_, v_h__1_314_, v_h__2_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_toSeq(lean_object* v_e_317_){
_start:
{
if (lean_obj_tag(v_e_317_) == 0)
{
lean_object* v_x_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_x_318_ = lean_ctor_get(v_e_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_e_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v_e_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_x_318_);
lean_dec(v_e_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_x_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_lhs_326_; lean_object* v_rhs_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_lhs_326_ = lean_ctor_get(v_e_317_, 0);
lean_inc_ref(v_lhs_326_);
v_rhs_327_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_rhs_327_);
lean_dec_ref(v_e_317_);
v___x_328_ = l_Lean_Grind_AC_Expr_toSeq(v_rhs_327_);
v___x_329_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_lhs_326_, v___x_328_);
lean_dec_ref(v_lhs_326_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_erase0(lean_object* v_s_330_){
_start:
{
if (lean_obj_tag(v_s_330_) == 0)
{
return v_s_330_;
}
else
{
lean_object* v_x_331_; lean_object* v_s_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_345_; 
v_x_331_ = lean_ctor_get(v_s_330_, 0);
v_s_332_ = lean_ctor_get(v_s_330_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_s_330_);
if (v_isSharedCheck_345_ == 0)
{
v___x_334_ = v_s_330_;
v_isShared_335_ = v_isSharedCheck_345_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_s_332_);
lean_inc(v_x_331_);
lean_dec(v_s_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_345_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_s_x27_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_s_x27_336_ = l_Lean_Grind_AC_Seq_erase0(v_s_332_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_eq(v_x_331_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0));
v___x_340_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_x27_336_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v_s_x27_336_);
v___x_342_ = v___x_334_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_x_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_s_x27_336_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec_ref(v_s_x27_336_);
lean_del_object(v___x_334_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_x_331_);
return v___x_344_;
}
}
else
{
lean_del_object(v___x_334_);
lean_dec(v_x_331_);
return v_s_x27_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(lean_object* v_s_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_){
_start:
{
if (lean_obj_tag(v_s_346_) == 0)
{
lean_object* v_x_349_; lean_object* v___x_350_; 
lean_dec(v_h__2_348_);
v_x_349_ = lean_ctor_get(v_s_346_, 0);
lean_inc(v_x_349_);
lean_dec_ref(v_s_346_);
v___x_350_ = lean_apply_1(v_h__1_347_, v_x_349_);
return v___x_350_;
}
else
{
lean_object* v_x_351_; lean_object* v_s_352_; lean_object* v___x_353_; 
lean_dec(v_h__1_347_);
v_x_351_ = lean_ctor_get(v_s_346_, 0);
lean_inc(v_x_351_);
v_s_352_ = lean_ctor_get(v_s_346_, 1);
lean_inc_ref(v_s_352_);
lean_dec_ref(v_s_346_);
v___x_353_ = lean_apply_2(v_h__2_348_, v_x_351_, v_s_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter(lean_object* v_motive_354_, lean_object* v_s_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(v_s_355_, v_h__1_356_, v_h__2_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_insert(lean_object* v_x_359_, lean_object* v_s_360_){
_start:
{
if (lean_obj_tag(v_s_360_) == 0)
{
lean_object* v_x_361_; uint8_t v___x_362_; 
v_x_361_ = lean_ctor_get(v_s_360_, 0);
v___x_362_ = l_Nat_blt(v_x_359_, v_x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
lean_inc(v_x_361_);
v_isSharedCheck_370_ = !lean_is_exclusive(v_s_360_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_s_360_, 0);
lean_dec(v_unused_371_);
v___x_364_ = v_s_360_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_s_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_x_359_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_x_359_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v_x_361_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
return v___x_368_;
}
}
}
else
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v_x_359_);
lean_ctor_set(v___x_372_, 1, v_s_360_);
return v___x_372_;
}
}
else
{
lean_object* v_x_373_; lean_object* v_s_374_; uint8_t v___x_375_; 
v_x_373_ = lean_ctor_get(v_s_360_, 0);
v_s_374_ = lean_ctor_get(v_s_360_, 1);
v___x_375_ = l_Nat_blt(v_x_359_, v_x_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
lean_inc_ref(v_s_374_);
lean_inc(v_x_373_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_s_360_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_s_360_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_s_360_, 0);
lean_dec(v_unused_385_);
v___x_377_ = v_s_360_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_dec(v_s_360_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_Grind_AC_Seq_insert(v_x_359_, v_s_374_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_x_373_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_x_359_);
lean_ctor_set(v___x_386_, 1, v_s_360_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort_x27(lean_object* v_s_387_, lean_object* v_acc_388_){
_start:
{
if (lean_obj_tag(v_s_387_) == 0)
{
lean_object* v_x_389_; lean_object* v___x_390_; 
v_x_389_ = lean_ctor_get(v_s_387_, 0);
lean_inc(v_x_389_);
lean_dec_ref(v_s_387_);
v___x_390_ = l_Lean_Grind_AC_Seq_insert(v_x_389_, v_acc_388_);
return v___x_390_;
}
else
{
lean_object* v_x_391_; lean_object* v_s_392_; lean_object* v___x_393_; 
v_x_391_ = lean_ctor_get(v_s_387_, 0);
lean_inc(v_x_391_);
v_s_392_ = lean_ctor_get(v_s_387_, 1);
lean_inc_ref(v_s_392_);
lean_dec_ref(v_s_387_);
v___x_393_ = l_Lean_Grind_AC_Seq_insert(v_x_391_, v_acc_388_);
v_s_387_ = v_s_392_;
v_acc_388_ = v___x_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sort(lean_object* v_s_395_){
_start:
{
if (lean_obj_tag(v_s_395_) == 0)
{
return v_s_395_;
}
else
{
lean_object* v_x_396_; lean_object* v_s_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_x_396_ = lean_ctor_get(v_s_395_, 0);
lean_inc(v_x_396_);
v_s_397_ = lean_ctor_get(v_s_395_, 1);
lean_inc_ref(v_s_397_);
lean_dec_ref(v_s_395_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_x_396_);
v___x_399_ = l_Lean_Grind_AC_Seq_sort_x27(v_s_397_, v___x_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_eraseDup(lean_object* v_s_400_){
_start:
{
if (lean_obj_tag(v_s_400_) == 0)
{
return v_s_400_;
}
else
{
lean_object* v_x_401_; lean_object* v_s_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_425_; 
v_x_401_ = lean_ctor_get(v_s_400_, 0);
v_s_402_ = lean_ctor_get(v_s_400_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_s_400_);
if (v_isSharedCheck_425_ == 0)
{
v___x_404_ = v_s_400_;
v_isShared_405_ = v_isSharedCheck_425_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_s_402_);
lean_inc(v_x_401_);
lean_dec(v_s_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_425_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_s_x27_406_; 
v_s_x27_406_ = l_Lean_Grind_AC_Seq_eraseDup(v_s_402_);
if (lean_obj_tag(v_s_x27_406_) == 0)
{
lean_object* v_x_407_; uint8_t v___x_408_; 
v_x_407_ = lean_ctor_get(v_s_x27_406_, 0);
lean_inc(v_x_407_);
v___x_408_ = lean_nat_dec_eq(v_x_401_, v_x_407_);
lean_dec(v_x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_410_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_s_x27_406_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_s_x27_406_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_404_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_s_x27_406_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_s_x27_406_, 0);
lean_dec(v_unused_419_);
v___x_413_ = v_s_x27_406_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_s_x27_406_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_x_401_);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_x_401_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_x_420_; uint8_t v___x_421_; 
v_x_420_ = lean_ctor_get(v_s_x27_406_, 0);
lean_inc(v_x_420_);
v___x_421_ = lean_nat_dec_eq(v_x_401_, v_x_420_);
lean_dec(v_x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_s_x27_406_);
v___x_423_ = v___x_404_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_s_x27_406_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_del_object(v___x_404_);
lean_dec(v_x_401_);
return v_s_x27_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_concat(lean_object* v_s_u2081_426_, lean_object* v_s_u2082_427_){
_start:
{
if (lean_obj_tag(v_s_u2081_426_) == 0)
{
lean_object* v_x_428_; lean_object* v___x_429_; 
v_x_428_ = lean_ctor_get(v_s_u2081_426_, 0);
lean_inc(v_x_428_);
lean_dec_ref(v_s_u2081_426_);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v_x_428_);
lean_ctor_set(v___x_429_, 1, v_s_u2082_427_);
return v___x_429_;
}
else
{
lean_object* v_x_430_; lean_object* v_s_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_x_430_ = lean_ctor_get(v_s_u2081_426_, 0);
v_s_431_ = lean_ctor_get(v_s_u2081_426_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_s_u2081_426_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v_s_u2081_426_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_s_431_);
lean_inc(v_x_430_);
lean_dec(v_s_u2081_426_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_Grind_AC_Seq_concat(v_s_431_, v_s_u2082_427_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_x_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel(lean_object* v_fuel_440_, lean_object* v_s_u2081_441_, lean_object* v_s_u2082_442_){
_start:
{
lean_object* v_zero_443_; uint8_t v_isZero_444_; 
v_zero_443_ = lean_unsigned_to_nat(0u);
v_isZero_444_ = lean_nat_dec_eq(v_fuel_440_, v_zero_443_);
if (v_isZero_444_ == 1)
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Grind_AC_Seq_concat(v_s_u2081_441_, v_s_u2082_442_);
return v___x_445_;
}
else
{
if (lean_obj_tag(v_s_u2081_441_) == 0)
{
if (lean_obj_tag(v_s_u2082_442_) == 0)
{
lean_object* v_x_446_; lean_object* v_x_447_; uint8_t v___x_448_; 
v_x_446_ = lean_ctor_get(v_s_u2081_441_, 0);
v_x_447_ = lean_ctor_get(v_s_u2082_442_, 0);
v___x_448_ = l_Nat_blt(v_x_446_, v_x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_inc(v_x_447_);
lean_dec_ref(v_s_u2082_442_);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v_x_447_);
lean_ctor_set(v___x_449_, 1, v_s_u2081_441_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
lean_inc(v_x_446_);
lean_dec_ref(v_s_u2081_441_);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v_x_446_);
lean_ctor_set(v___x_450_, 1, v_s_u2082_442_);
return v___x_450_;
}
}
else
{
lean_object* v_x_451_; lean_object* v___x_452_; 
v_x_451_ = lean_ctor_get(v_s_u2081_441_, 0);
lean_inc(v_x_451_);
lean_dec_ref(v_s_u2081_441_);
v___x_452_ = l_Lean_Grind_AC_Seq_insert(v_x_451_, v_s_u2082_442_);
return v___x_452_;
}
}
else
{
if (lean_obj_tag(v_s_u2082_442_) == 0)
{
lean_object* v_x_453_; lean_object* v___x_454_; 
v_x_453_ = lean_ctor_get(v_s_u2082_442_, 0);
lean_inc(v_x_453_);
lean_dec_ref(v_s_u2082_442_);
v___x_454_ = l_Lean_Grind_AC_Seq_insert(v_x_453_, v_s_u2081_441_);
return v___x_454_;
}
else
{
lean_object* v_x_455_; lean_object* v_s_456_; lean_object* v_x_457_; lean_object* v_s_458_; lean_object* v_one_459_; lean_object* v_n_460_; uint8_t v___x_461_; 
v_x_455_ = lean_ctor_get(v_s_u2081_441_, 0);
v_s_456_ = lean_ctor_get(v_s_u2081_441_, 1);
v_x_457_ = lean_ctor_get(v_s_u2082_442_, 0);
v_s_458_ = lean_ctor_get(v_s_u2082_442_, 1);
v_one_459_ = lean_unsigned_to_nat(1u);
v_n_460_ = lean_nat_sub(v_fuel_440_, v_one_459_);
v___x_461_ = l_Nat_blt(v_x_455_, v_x_457_);
if (v___x_461_ == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
lean_inc_ref(v_s_458_);
lean_inc(v_x_457_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_u2082_442_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v_s_u2082_442_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_u2082_442_, 0);
lean_dec(v_unused_471_);
v___x_463_ = v_s_u2082_442_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_s_u2082_442_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_460_, v_s_u2081_441_, v_s_458_);
lean_dec(v_n_460_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_x_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
lean_inc_ref(v_s_456_);
lean_inc(v_x_455_);
v_isSharedCheck_479_ = !lean_is_exclusive(v_s_u2081_441_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_480_ = lean_ctor_get(v_s_u2081_441_, 1);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_s_u2081_441_, 0);
lean_dec(v_unused_481_);
v___x_473_ = v_s_u2081_441_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_s_u2081_441_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_460_, v_s_456_, v_s_u2082_442_);
lean_dec(v_n_460_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_unionFuel___boxed(lean_object* v_fuel_482_, lean_object* v_s_u2081_483_, lean_object* v_s_u2082_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Grind_AC_Seq_unionFuel(v_fuel_482_, v_s_u2081_483_, v_s_u2082_484_);
lean_dec(v_fuel_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(lean_object* v_fuel_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_){
_start:
{
lean_object* v_zero_489_; uint8_t v_isZero_490_; 
v_zero_489_ = lean_unsigned_to_nat(0u);
v_isZero_490_ = lean_nat_dec_eq(v_fuel_486_, v_zero_489_);
if (v_isZero_490_ == 1)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_488_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_apply_1(v_h__1_487_, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_one_493_; lean_object* v_n_494_; lean_object* v___x_495_; 
lean_dec(v_h__1_487_);
v_one_493_ = lean_unsigned_to_nat(1u);
v_n_494_ = lean_nat_sub(v_fuel_486_, v_one_493_);
v___x_495_ = lean_apply_1(v_h__2_488_, v_n_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg___boxed(lean_object* v_fuel_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(v_fuel_496_, v_h__1_497_, v_h__2_498_);
lean_dec(v_fuel_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(lean_object* v_motive_500_, lean_object* v_fuel_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(v_fuel_501_, v_h__1_502_, v_h__2_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___boxed(lean_object* v_motive_505_, lean_object* v_fuel_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(v_motive_505_, v_fuel_506_, v_h__1_507_, v_h__2_508_);
lean_dec(v_fuel_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(lean_object* v_s_u2081_510_, lean_object* v_s_u2082_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_, lean_object* v_h__4_515_){
_start:
{
if (lean_obj_tag(v_s_u2081_510_) == 0)
{
lean_dec(v_h__4_515_);
lean_dec(v_h__3_514_);
if (lean_obj_tag(v_s_u2082_511_) == 0)
{
lean_object* v_x_516_; lean_object* v_x_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_513_);
v_x_516_ = lean_ctor_get(v_s_u2081_510_, 0);
lean_inc(v_x_516_);
lean_dec_ref(v_s_u2081_510_);
v_x_517_ = lean_ctor_get(v_s_u2082_511_, 0);
lean_inc(v_x_517_);
lean_dec_ref(v_s_u2082_511_);
v___x_518_ = lean_apply_2(v_h__1_512_, v_x_516_, v_x_517_);
return v___x_518_;
}
else
{
lean_object* v_x_519_; lean_object* v_x_520_; lean_object* v_s_521_; lean_object* v___x_522_; 
lean_dec(v_h__1_512_);
v_x_519_ = lean_ctor_get(v_s_u2081_510_, 0);
lean_inc(v_x_519_);
lean_dec_ref(v_s_u2081_510_);
v_x_520_ = lean_ctor_get(v_s_u2082_511_, 0);
lean_inc(v_x_520_);
v_s_521_ = lean_ctor_get(v_s_u2082_511_, 1);
lean_inc_ref(v_s_521_);
lean_dec_ref(v_s_u2082_511_);
v___x_522_ = lean_apply_3(v_h__2_513_, v_x_519_, v_x_520_, v_s_521_);
return v___x_522_;
}
}
else
{
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
if (lean_obj_tag(v_s_u2082_511_) == 0)
{
lean_object* v_x_523_; lean_object* v_s_524_; lean_object* v_x_525_; lean_object* v___x_526_; 
lean_dec(v_h__4_515_);
v_x_523_ = lean_ctor_get(v_s_u2081_510_, 0);
lean_inc(v_x_523_);
v_s_524_ = lean_ctor_get(v_s_u2081_510_, 1);
lean_inc_ref(v_s_524_);
lean_dec_ref(v_s_u2081_510_);
v_x_525_ = lean_ctor_get(v_s_u2082_511_, 0);
lean_inc(v_x_525_);
lean_dec_ref(v_s_u2082_511_);
v___x_526_ = lean_apply_3(v_h__3_514_, v_x_523_, v_s_524_, v_x_525_);
return v___x_526_;
}
else
{
lean_object* v_x_527_; lean_object* v_s_528_; lean_object* v_x_529_; lean_object* v_s_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_514_);
v_x_527_ = lean_ctor_get(v_s_u2081_510_, 0);
lean_inc(v_x_527_);
v_s_528_ = lean_ctor_get(v_s_u2081_510_, 1);
lean_inc_ref(v_s_528_);
lean_dec_ref(v_s_u2081_510_);
v_x_529_ = lean_ctor_get(v_s_u2082_511_, 0);
lean_inc(v_x_529_);
v_s_530_ = lean_ctor_get(v_s_u2082_511_, 1);
lean_inc_ref(v_s_530_);
lean_dec_ref(v_s_u2082_511_);
v___x_531_ = lean_apply_4(v_h__4_515_, v_x_527_, v_s_528_, v_x_529_, v_s_530_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter(lean_object* v_motive_532_, lean_object* v_s_u2081_533_, lean_object* v_s_u2082_534_, lean_object* v_h__1_535_, lean_object* v_h__2_536_, lean_object* v_h__3_537_, lean_object* v_h__4_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(v_s_u2081_533_, v_s_u2082_534_, v_h__1_535_, v_h__2_536_, v_h__3_537_, v_h__4_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Grind_AC_hugeFuel(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(1000000u);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_union(lean_object* v_s_u2081_541_, lean_object* v_s_u2082_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(1000000u);
v___x_544_ = l_Lean_Grind_AC_Seq_unionFuel(v___x_543_, v_s_u2081_541_, v_s_u2082_542_);
return v___x_544_;
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
