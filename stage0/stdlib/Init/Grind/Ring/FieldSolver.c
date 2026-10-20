// Lean compiler output
// Module: Init.Grind.Ring.FieldSolver
// Imports: public import Init.Grind.Ring.CommSolver public import Init.Grind.Ordered.Field public import Init.Data.Nat.Gcd import Init.LawfulBEqTactics import Init.Data.Nat.Lemmas import Init.Omega
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
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPolyQ_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPolyQ_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instBEqPolyQ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instBEqPolyQ_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instBEqPolyQ___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPolyQ___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instBEqPolyQ = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPolyQ___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPolyQ_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7;
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "den"};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instReprPolyQ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instReprPolyQ_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instReprPolyQ___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instReprPolyQ = (const lean_object*)&l_Lean_Grind_CommRing_instReprPolyQ___closed__0_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPolyQ_default;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPolyQ;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_cancelInv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_cancelInv___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_cancelInv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_cancelInv___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInvs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_reduce(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toPolyQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_cancelInvs__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_cancelInvs__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normA__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normA__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_toPolyQ__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normQ__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normQ__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPolyQ_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_num_3_; lean_object* v_den_4_; lean_object* v_num_5_; lean_object* v_den_6_; uint8_t v___x_7_; 
v_num_3_ = lean_ctor_get(v_x_1_, 0);
v_den_4_ = lean_ctor_get(v_x_1_, 1);
v_num_5_ = lean_ctor_get(v_x_2_, 0);
v_den_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_num_3_, v_num_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_den_4_, v_den_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPolyQ_beq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPolyQ_repr_spec__0(lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_nat_to_int(v_a_15_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(7u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0));
v___x_40_ = lean_string_length(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(lean_object* v_x_47_){
_start:
{
lean_object* v_num_48_; lean_object* v_den_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_83_; 
v_num_48_ = lean_ctor_get(v_x_47_, 0);
v_den_49_ = lean_ctor_get(v_x_47_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_83_ == 0)
{
v___x_51_ = v_x_47_;
v_isShared_52_ = v_isSharedCheck_83_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_den_49_);
lean_inc(v_num_48_);
lean_dec(v_x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_83_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_53_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5));
v___x_54_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6));
v___x_55_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_num_48_, v___x_56_);
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 4);
lean_ctor_set(v___x_51_, 1, v___x_57_);
lean_ctor_set(v___x_51_, 0, v___x_55_);
v___x_59_ = v___x_51_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_82_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_60_ = 0;
v___x_61_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set_uint8(v___x_61_, sizeof(void*)*1, v___x_60_);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_54_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9));
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_box(1);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11));
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_53_);
v___x_70_ = l_Nat_reprFast(v_den_49_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_55_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_60_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_69_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14);
v___x_76_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15));
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_74_);
v___x_78_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_75_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_60_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(v_x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Grind_CommRing_instReprPolyQ_repr(v_x_87_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_89_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Grind_CommRing_instInhabitedPolyQ_default;
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(lean_object* v_ctx_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
if (lean_obj_tag(v_a_98_) == 0)
{
lean_object* v___x_100_; 
v___x_100_ = l_List_reverse___redArg(v_a_99_);
return v___x_100_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_112_; 
v_head_101_ = lean_ctor_get(v_a_98_, 0);
v_tail_102_ = lean_ctor_get(v_a_98_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_a_98_);
if (v_isSharedCheck_112_ == 0)
{
v___x_104_ = v_a_98_;
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_tail_102_);
lean_inc(v_head_101_);
lean_dec(v_a_98_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_fst_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v_fst_106_ = lean_ctor_get(v_head_101_, 0);
lean_inc(v_fst_106_);
lean_dec(v_head_101_);
v___x_107_ = l_Lean_RArray_getImpl___redArg(v_ctx_97_, v_fst_106_);
lean_dec(v_fst_106_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_a_99_);
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_a_99_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
v_a_98_ = v_tail_102_;
v_a_99_ = v___x_109_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg___boxed(lean_object* v_ctx_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_ctx_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(lean_object* v_ctx_117_, lean_object* v_invs_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_box(0);
v___x_120_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_117_, v_invs_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg___boxed(lean_object* v_ctx_121_, lean_object* v_invs_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_121_, v_invs_122_);
lean_dec_ref(v_ctx_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars(lean_object* v_00_u03b1_124_, lean_object* v_ctx_125_, lean_object* v_invs_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_125_, v_invs_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___boxed(lean_object* v_00_u03b1_128_, lean_object* v_ctx_129_, lean_object* v_invs_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Grind_CommRing_InvVars_denoteVars(v_00_u03b1_128_, v_ctx_129_, v_invs_130_);
lean_dec_ref(v_ctx_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(lean_object* v_00_u03b1_132_, lean_object* v_ctx_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_133_, v_a_134_, v_a_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___boxed(lean_object* v_00_u03b1_137_, lean_object* v_ctx_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(v_00_u03b1_137_, v_ctx_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_ctx_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0(lean_object* v_toSemiring_142_, lean_object* v_toInv_143_, lean_object* v_p_144_){
_start:
{
lean_object* v_ofNat_145_; lean_object* v_snd_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_ofNat_145_ = lean_ctor_get(v_toSemiring_142_, 3);
lean_inc(v_ofNat_145_);
lean_dec_ref(v_toSemiring_142_);
v_snd_146_ = lean_ctor_get(v_p_144_, 1);
lean_inc(v_snd_146_);
lean_dec_ref(v_p_144_);
v___x_147_ = lean_apply_1(v_ofNat_145_, v_snd_146_);
v___x_148_ = lean_apply_1(v_toInv_143_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(lean_object* v_inst_149_, lean_object* v_invs_150_){
_start:
{
lean_object* v_toCommRing_151_; lean_object* v_toInv_152_; lean_object* v_toSemiring_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_toCommRing_151_ = lean_ctor_get(v_inst_149_, 0);
lean_inc_ref(v_toCommRing_151_);
v_toInv_152_ = lean_ctor_get(v_inst_149_, 1);
lean_inc(v_toInv_152_);
lean_dec_ref(v_inst_149_);
v_toSemiring_153_ = lean_ctor_get(v_toCommRing_151_, 0);
lean_inc_ref(v_toSemiring_153_);
lean_dec_ref(v_toCommRing_151_);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0), 3, 2);
lean_closure_set(v___f_154_, 0, v_toSemiring_153_);
lean_closure_set(v___f_154_, 1, v_toInv_152_);
v___x_155_ = lean_box(0);
v___x_156_ = l_List_mapTR_loop___redArg(v___f_154_, v_invs_150_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_invs_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(v_inst_158_, v_invs_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelInv(lean_object* v_x_161_, lean_object* v_y_162_, lean_object* v_m_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_eq(v_x_161_, v_y_162_);
if (v___x_164_ == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_a_165_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_163_, v_x_161_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_nat_dec_eq(v_a_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v_b_168_; uint8_t v___x_169_; 
v_b_168_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_163_, v_y_162_);
v___x_169_ = lean_nat_dec_eq(v_b_168_, v___x_166_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v_m_x27_171_; uint8_t v___x_172_; 
v___x_170_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_163_, v_x_161_);
v_m_x27_171_ = l_Lean_Grind_CommRing_Mon_cancelVar(v___x_170_, v_y_162_);
v___x_172_ = lean_nat_dec_lt(v_a_165_, v_b_168_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
lean_dec(v_y_162_);
v___x_173_ = lean_nat_dec_lt(v_b_168_, v_a_165_);
if (v___x_173_ == 0)
{
lean_dec(v_b_168_);
lean_dec(v_a_165_);
lean_dec(v_x_161_);
return v_m_x27_171_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_nat_sub(v_a_165_, v_b_168_);
lean_dec(v_b_168_);
lean_dec(v_a_165_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_x_161_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_175_, v_m_x27_171_);
return v___x_176_;
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_x_161_);
v___x_177_ = lean_nat_sub(v_b_168_, v_a_165_);
lean_dec(v_a_165_);
lean_dec(v_b_168_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_y_162_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_178_, v_m_x27_171_);
return v___x_179_;
}
}
else
{
lean_dec(v_b_168_);
lean_dec(v_a_165_);
lean_dec(v_y_162_);
lean_dec(v_x_161_);
return v_m_163_;
}
}
else
{
lean_dec(v_a_165_);
lean_dec(v_y_162_);
lean_dec(v_x_161_);
return v_m_163_;
}
}
else
{
lean_dec(v_y_162_);
lean_dec(v_x_161_);
return v_m_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv_go(lean_object* v_x_180_, lean_object* v_y_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
if (lean_obj_tag(v_a_182_) == 0)
{
lean_object* v_k_184_; lean_object* v___x_185_; 
lean_dec(v_y_181_);
lean_dec(v_x_180_);
v_k_184_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_k_184_);
lean_dec_ref_known(v_a_182_, 1);
v___x_185_ = l_Lean_Grind_CommRing_Poly_addConst(v_a_183_, v_k_184_);
lean_dec(v_k_184_);
return v___x_185_;
}
else
{
lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v_p_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_k_186_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_k_186_);
v_v_187_ = lean_ctor_get(v_a_182_, 1);
lean_inc(v_v_187_);
v_p_188_ = lean_ctor_get(v_a_182_, 2);
lean_inc_ref(v_p_188_);
lean_dec_ref_known(v_a_182_, 3);
lean_inc(v_y_181_);
lean_inc(v_x_180_);
v___x_189_ = l_Lean_Grind_CommRing_Mon_cancelInv(v_x_180_, v_y_181_, v_v_187_);
v___x_190_ = l_Lean_Grind_CommRing_Poly_insert(v_k_186_, v___x_189_, v_a_183_);
v_a_182_ = v_p_188_;
v_a_183_ = v___x_190_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__0, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv(lean_object* v_x_196_, lean_object* v_y_197_, lean_object* v_p_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__1, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1);
v___x_200_ = l_Lean_Grind_CommRing_Poly_cancelInv_go(v_x_196_, v_y_197_, v_p_198_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
return v_x_201_;
}
else
{
lean_object* v_head_203_; lean_object* v_tail_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_207_; 
v_head_203_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_head_203_);
v_tail_204_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_tail_204_);
lean_dec_ref_known(v_x_202_, 2);
v_fst_205_ = lean_ctor_get(v_head_203_, 0);
lean_inc(v_fst_205_);
v_snd_206_ = lean_ctor_get(v_head_203_, 1);
lean_inc(v_snd_206_);
lean_dec(v_head_203_);
v___x_207_ = l_Lean_Grind_CommRing_Poly_cancelInv(v_snd_206_, v_fst_205_, v_x_201_);
v_x_201_ = v___x_207_;
v_x_202_ = v_tail_204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInvs(lean_object* v_p_209_, lean_object* v_ainvs_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_209_, v_ainvs_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg(lean_object* v_inst_212_, lean_object* v_ctx_213_, lean_object* v_q_214_){
_start:
{
lean_object* v_toCommRing_215_; lean_object* v_toSemiring_216_; lean_object* v_toInv_217_; lean_object* v_toMul_218_; lean_object* v_natCast_219_; lean_object* v_num_220_; lean_object* v_den_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_toCommRing_215_ = lean_ctor_get(v_inst_212_, 0);
lean_inc_ref(v_toCommRing_215_);
v_toSemiring_216_ = lean_ctor_get(v_toCommRing_215_, 0);
v_toInv_217_ = lean_ctor_get(v_inst_212_, 1);
lean_inc(v_toInv_217_);
lean_dec_ref(v_inst_212_);
v_toMul_218_ = lean_ctor_get(v_toSemiring_216_, 1);
lean_inc(v_toMul_218_);
v_natCast_219_ = lean_ctor_get(v_toSemiring_216_, 2);
lean_inc(v_natCast_219_);
v_num_220_ = lean_ctor_get(v_q_214_, 0);
lean_inc_ref(v_num_220_);
v_den_221_ = lean_ctor_get(v_q_214_, 1);
lean_inc(v_den_221_);
lean_dec_ref(v_q_214_);
v___x_222_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_toCommRing_215_, v_ctx_213_, v_num_220_);
v___x_223_ = lean_apply_1(v_natCast_219_, v_den_221_);
v___x_224_ = lean_apply_1(v_toInv_217_, v___x_223_);
v___x_225_ = lean_apply_2(v_toMul_218_, v___x_222_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg___boxed(lean_object* v_inst_226_, lean_object* v_ctx_227_, lean_object* v_q_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_226_, v_ctx_227_, v_q_228_);
lean_dec_ref(v_ctx_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote(lean_object* v_00_u03b1_230_, lean_object* v_inst_231_, lean_object* v_ctx_232_, lean_object* v_q_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_231_, v_ctx_232_, v_q_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___boxed(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_ctx_237_, lean_object* v_q_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Grind_CommRing_PolyQ_denote(v_00_u03b1_235_, v_inst_236_, v_ctx_237_, v_q_238_);
lean_dec_ref(v_ctx_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv(lean_object* v_p_240_, lean_object* v_x_241_, lean_object* v_c_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_nat_dec_eq(v_c_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v_n_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_n_245_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_240_, v_x_241_);
lean_inc(v_c_242_);
v___x_246_ = lean_nat_to_int(v_c_242_);
v___x_247_ = lean_nat_pow(v_c_242_, v_n_245_);
lean_dec(v_n_245_);
lean_dec(v_c_242_);
lean_inc(v___x_247_);
v___x_248_ = lean_nat_to_int(v___x_247_);
v___x_249_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_248_, v_p_240_);
lean_dec(v___x_248_);
v___x_250_ = l_Lean_Grind_CommRing_Poly_cancelVar(v___x_246_, v_x_241_, v___x_249_);
lean_dec(v___x_246_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_247_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_c_242_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_p_240_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv___boxed(lean_object* v_p_254_, lean_object* v_x_255_, lean_object* v_c_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Grind_CommRing_Poly_substInv(v_p_254_, v_x_255_, v_c_256_);
lean_dec(v_x_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv(lean_object* v_q_258_, lean_object* v_x_259_, lean_object* v_c_260_){
_start:
{
lean_object* v_num_261_; lean_object* v_den_262_; lean_object* v_q_x27_263_; lean_object* v_num_264_; lean_object* v_den_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_num_261_ = lean_ctor_get(v_q_258_, 0);
lean_inc_ref(v_num_261_);
v_den_262_ = lean_ctor_get(v_q_258_, 1);
lean_inc(v_den_262_);
lean_dec_ref(v_q_258_);
v_q_x27_263_ = l_Lean_Grind_CommRing_Poly_substInv(v_num_261_, v_x_259_, v_c_260_);
v_num_264_ = lean_ctor_get(v_q_x27_263_, 0);
v_den_265_ = lean_ctor_get(v_q_x27_263_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_q_x27_263_);
if (v_isSharedCheck_273_ == 0)
{
v___x_267_ = v_q_x27_263_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_den_265_);
lean_inc(v_num_264_);
lean_dec(v_q_x27_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_nat_mul(v_den_262_, v_den_265_);
lean_dec(v_den_265_);
lean_dec(v_den_262_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_num_264_);
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
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv___boxed(lean_object* v_q_274_, lean_object* v_x_275_, lean_object* v_c_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_q_274_, v_x_275_, v_c_276_);
lean_dec(v_x_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_reduce(lean_object* v_q_278_){
_start:
{
lean_object* v_num_279_; lean_object* v_den_280_; lean_object* v___x_281_; lean_object* v_g_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_num_279_ = lean_ctor_get(v_q_278_, 0);
v_den_280_ = lean_ctor_get(v_q_278_, 1);
v___x_281_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_num_279_);
v_g_282_ = lean_nat_gcd(v___x_281_, v_den_280_);
lean_dec(v___x_281_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_dec_le(v_g_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v_num_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
lean_inc(v_g_282_);
v___x_285_ = lean_nat_to_int(v_g_282_);
lean_inc_ref(v_num_279_);
v_num_286_ = l_Lean_Grind_CommRing_Poly_divConst(v_num_279_, v___x_285_);
lean_inc_ref(v_num_286_);
v___x_287_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_285_, v_num_286_);
lean_dec(v___x_285_);
v___x_288_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_287_, v_num_279_);
lean_dec_ref(v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_num_286_);
lean_dec(v_g_282_);
return v_q_278_;
}
else
{
lean_object* v_den_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_den_289_ = lean_nat_div(v_den_280_, v_g_282_);
v___x_290_ = lean_nat_mul(v_den_289_, v_g_282_);
lean_dec(v_g_282_);
v___x_291_ = lean_nat_dec_eq(v___x_290_, v_den_280_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_den_289_);
lean_dec_ref(v_num_286_);
return v_q_278_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v_q_278_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v_q_278_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_q_278_, 0);
lean_dec(v_unused_300_);
v___x_293_ = v_q_278_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_q_278_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_den_289_);
lean_ctor_set(v___x_293_, 0, v_num_286_);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_num_286_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_den_289_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_dec(v_g_282_);
return v_q_278_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
return v_x_301_;
}
else
{
lean_object* v_head_303_; lean_object* v_tail_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; 
v_head_303_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_head_303_);
v_tail_304_ = lean_ctor_get(v_x_302_, 1);
lean_inc(v_tail_304_);
lean_dec_ref_known(v_x_302_, 2);
v_fst_305_ = lean_ctor_get(v_head_303_, 0);
lean_inc(v_fst_305_);
v_snd_306_ = lean_ctor_get(v_head_303_, 1);
lean_inc(v_snd_306_);
lean_dec(v_head_303_);
v___x_307_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_x_301_, v_fst_305_, v_snd_306_);
lean_dec(v_fst_305_);
v_x_301_ = v___x_307_;
v_x_302_ = v_tail_304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toPolyQ(lean_object* v_p_309_, lean_object* v_invs_310_, lean_object* v_ainvs_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_312_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_309_, v_ainvs_311_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(v___x_314_, v_invs_310_);
v___x_316_ = l_Lean_Grind_CommRing_PolyQ_reduce(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ(lean_object* v_e_317_, lean_object* v_invs_318_, lean_object* v_ainvs_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = l_Lean_Grind_CommRing_Expr_toPoly(v_e_317_);
v___x_321_ = l_Lean_Grind_CommRing_Poly_toPolyQ(v___x_320_, v_invs_318_, v_ainvs_319_);
return v___x_321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_cancelInvs__cert(lean_object* v_ainvs_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_325_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_323_);
lean_inc(v_ainvs_322_);
v___x_326_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_325_, v_ainvs_322_);
v___x_327_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_324_);
v___x_328_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_327_, v_ainvs_322_);
v___x_329_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_326_, v___x_328_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v___x_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_cancelInvs__cert___boxed(lean_object* v_ainvs_330_, lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lean_Grind_CommRing_Expr_cancelInvs__cert(v_ainvs_330_, v_a_331_, v_b_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normA__cert(lean_object* v_ainvs_335_, lean_object* v_lhs_336_, lean_object* v_rhs_337_, lean_object* v_lhs_x27_338_, lean_object* v_rhs_x27_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_340_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_340_, 0, v_lhs_336_);
lean_ctor_set(v___x_340_, 1, v_rhs_337_);
v___x_341_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_340_);
v___x_342_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_341_, v_ainvs_335_);
v___x_343_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_343_, 0, v_lhs_x27_338_);
lean_ctor_set(v___x_343_, 1, v_rhs_x27_339_);
v___x_344_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_343_);
v___x_345_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_342_, v___x_344_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normA__cert___boxed(lean_object* v_ainvs_346_, lean_object* v_lhs_347_, lean_object* v_rhs_348_, lean_object* v_lhs_x27_349_, lean_object* v_rhs_x27_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Grind_CommRing_normA__cert(v_ainvs_346_, v_lhs_347_, v_rhs_348_, v_lhs_x27_349_, v_rhs_x27_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_toPolyQ__cert(lean_object* v_invs_353_, lean_object* v_ainvs_354_, lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_inc(v_ainvs_354_);
lean_inc(v_invs_353_);
v___x_357_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_a_355_, v_invs_353_, v_ainvs_354_);
v___x_358_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_b_356_, v_invs_353_, v_ainvs_354_);
v___x_359_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
lean_dec_ref(v___x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ__cert___boxed(lean_object* v_invs_360_, lean_object* v_ainvs_361_, lean_object* v_a_362_, lean_object* v_b_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Lean_Grind_CommRing_Expr_toPolyQ__cert(v_invs_360_, v_ainvs_361_, v_a_362_, v_b_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normQ__cert(lean_object* v_invs_366_, lean_object* v_ainvs_367_, lean_object* v_lhs_368_, lean_object* v_rhs_369_, lean_object* v_lhs_x27_370_, lean_object* v_rhs_x27_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_num_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v___x_372_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_372_, 0, v_lhs_368_);
lean_ctor_set(v___x_372_, 1, v_rhs_369_);
v___x_373_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v___x_372_, v_invs_366_, v_ainvs_367_);
v_num_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_373_, 1);
lean_dec(v_unused_384_);
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_num_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 6);
lean_ctor_set(v___x_376_, 1, v_rhs_x27_371_);
lean_ctor_set(v___x_376_, 0, v_lhs_x27_370_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_lhs_x27_370_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_rhs_x27_371_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_379_);
v___x_381_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_num_374_, v___x_380_);
lean_dec_ref(v___x_380_);
lean_dec_ref(v_num_374_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normQ__cert___boxed(lean_object* v_invs_385_, lean_object* v_ainvs_386_, lean_object* v_lhs_387_, lean_object* v_rhs_388_, lean_object* v_lhs_x27_389_, lean_object* v_rhs_x27_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lean_Grind_CommRing_normQ__cert(v_invs_385_, v_ainvs_386_, v_lhs_387_, v_rhs_388_, v_lhs_x27_389_, v_rhs_x27_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Field(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_FieldSolver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_CommRing_instInhabitedPolyQ_default = _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPolyQ_default);
l_Lean_Grind_CommRing_instInhabitedPolyQ = _init_l_Lean_Grind_CommRing_instInhabitedPolyQ();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPolyQ);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_FieldSolver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Field(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_FieldSolver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_FieldSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_FieldSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_FieldSolver(builtin);
}
#ifdef __cplusplus
}
#endif
