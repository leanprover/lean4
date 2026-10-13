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
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_cancelInv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_cancelInv___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_cancelInv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_cancelInv___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Poly_cancelInv_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Poly_cancelInv_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter___redArg(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_){
_start:
{
lean_object* v_num_18_; lean_object* v_den_19_; lean_object* v_num_20_; lean_object* v_den_21_; lean_object* v___x_22_; 
v_num_18_ = lean_ctor_get(v_x_15_, 0);
lean_inc_ref(v_num_18_);
v_den_19_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_den_19_);
lean_dec_ref(v_x_15_);
v_num_20_ = lean_ctor_get(v_x_16_, 0);
lean_inc_ref(v_num_20_);
v_den_21_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_den_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_4(v_h__1_17_, v_num_18_, v_den_19_, v_num_20_, v_den_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v_num_28_; lean_object* v_den_29_; lean_object* v_num_30_; lean_object* v_den_31_; lean_object* v___x_32_; 
v_num_28_ = lean_ctor_get(v_x_24_, 0);
lean_inc_ref(v_num_28_);
v_den_29_ = lean_ctor_get(v_x_24_, 1);
lean_inc(v_den_29_);
lean_dec_ref(v_x_24_);
v_num_30_ = lean_ctor_get(v_x_25_, 0);
lean_inc_ref(v_num_30_);
v_den_31_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_den_31_);
lean_dec_ref(v_x_25_);
v___x_32_ = lean_apply_4(v_h__1_26_, v_num_28_, v_den_29_, v_num_30_, v_den_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter___boxed(lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_instBEqPolyQ_beq_match__1_splitter(v_motive_33_, v_x_34_, v_x_35_, v_h__1_36_, v_h__2_37_);
lean_dec(v_h__2_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPolyQ_repr_spec__0(lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_nat_to_int(v_a_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(7u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0));
v___x_64_ = lean_string_length(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(lean_object* v_x_71_){
_start:
{
lean_object* v_num_72_; lean_object* v_den_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_107_; 
v_num_72_ = lean_ctor_get(v_x_71_, 0);
v_den_73_ = lean_ctor_get(v_x_71_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_107_ == 0)
{
v___x_75_ = v_x_71_;
v_isShared_76_ = v_isSharedCheck_107_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_den_73_);
lean_inc(v_num_72_);
lean_dec(v_x_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_107_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_77_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5));
v___x_78_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6));
v___x_79_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_num_72_, v___x_80_);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 4);
lean_ctor_set(v___x_75_, 1, v___x_81_);
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_83_ = v___x_75_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_81_);
v___x_83_ = v_reuseFailAlloc_106_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_84_ = 0;
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_84_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_78_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9));
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_box(1);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11));
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_77_);
v___x_94_ = l_Nat_reprFast(v_den_73_);
v___x_95_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_79_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_84_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_93_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14);
v___x_100_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15));
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_98_);
v___x_102_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16));
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_84_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(v_x_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___boxed(lean_object* v_x_111_, lean_object* v_prec_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Grind_CommRing_instReprPolyQ_repr(v_x_111_, v_prec_112_);
lean_dec(v_prec_112_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Grind_CommRing_instInhabitedPolyQ_default;
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(lean_object* v_ctx_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
if (lean_obj_tag(v_a_122_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = l_List_reverse___redArg(v_a_123_);
return v___x_124_;
}
else
{
lean_object* v_head_125_; lean_object* v_tail_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v_head_125_ = lean_ctor_get(v_a_122_, 0);
v_tail_126_ = lean_ctor_get(v_a_122_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_122_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v_a_122_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_tail_126_);
lean_inc(v_head_125_);
lean_dec(v_a_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_fst_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_fst_130_ = lean_ctor_get(v_head_125_, 0);
lean_inc(v_fst_130_);
lean_dec(v_head_125_);
v___x_131_ = l_Lean_RArray_getImpl___redArg(v_ctx_121_, v_fst_130_);
lean_dec(v_fst_130_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_a_123_);
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_a_123_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v_a_122_ = v_tail_126_;
v_a_123_ = v___x_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg___boxed(lean_object* v_ctx_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_137_, v_a_138_, v_a_139_);
lean_dec_ref(v_ctx_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(lean_object* v_ctx_141_, lean_object* v_invs_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_box(0);
v___x_144_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_141_, v_invs_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg___boxed(lean_object* v_ctx_145_, lean_object* v_invs_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_145_, v_invs_146_);
lean_dec_ref(v_ctx_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars(lean_object* v_00_u03b1_148_, lean_object* v_ctx_149_, lean_object* v_invs_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_149_, v_invs_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___boxed(lean_object* v_00_u03b1_152_, lean_object* v_ctx_153_, lean_object* v_invs_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Grind_CommRing_InvVars_denoteVars(v_00_u03b1_152_, v_ctx_153_, v_invs_154_);
lean_dec_ref(v_ctx_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(lean_object* v_00_u03b1_156_, lean_object* v_ctx_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_157_, v_a_158_, v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___boxed(lean_object* v_00_u03b1_161_, lean_object* v_ctx_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(v_00_u03b1_161_, v_ctx_162_, v_a_163_, v_a_164_);
lean_dec_ref(v_ctx_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0(lean_object* v_toSemiring_166_, lean_object* v_toInv_167_, lean_object* v_p_168_){
_start:
{
lean_object* v_ofNat_169_; lean_object* v_snd_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_ofNat_169_ = lean_ctor_get(v_toSemiring_166_, 3);
lean_inc(v_ofNat_169_);
lean_dec_ref(v_toSemiring_166_);
v_snd_170_ = lean_ctor_get(v_p_168_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v_p_168_);
v___x_171_ = lean_apply_1(v_ofNat_169_, v_snd_170_);
v___x_172_ = lean_apply_1(v_toInv_167_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(lean_object* v_inst_173_, lean_object* v_invs_174_){
_start:
{
lean_object* v_toCommRing_175_; lean_object* v_toInv_176_; lean_object* v_toSemiring_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toCommRing_175_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toCommRing_175_);
v_toInv_176_ = lean_ctor_get(v_inst_173_, 1);
lean_inc(v_toInv_176_);
lean_dec_ref(v_inst_173_);
v_toSemiring_177_ = lean_ctor_get(v_toCommRing_175_, 0);
lean_inc_ref(v_toSemiring_177_);
lean_dec_ref(v_toCommRing_175_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0), 3, 2);
lean_closure_set(v___f_178_, 0, v_toSemiring_177_);
lean_closure_set(v___f_178_, 1, v_toInv_176_);
v___x_179_ = lean_box(0);
v___x_180_ = l_List_mapTR_loop___redArg(v___f_178_, v_invs_174_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_invs_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(v_inst_182_, v_invs_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_h__2_187_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_h__1_186_, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v_p_190_; lean_object* v_m_191_; lean_object* v___x_192_; 
lean_dec(v_h__1_186_);
v_p_190_ = lean_ctor_get(v_x_185_, 0);
lean_inc_ref(v_p_190_);
v_m_191_ = lean_ctor_get(v_x_185_, 1);
lean_inc(v_m_191_);
lean_dec_ref_known(v_x_185_, 2);
v___x_192_ = lean_apply_2(v_h__2_187_, v_p_190_, v_m_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_193_, lean_object* v_x_194_, lean_object* v_h__1_195_, lean_object* v_h__2_196_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__2_196_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__1_195_, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_p_199_; lean_object* v_m_200_; lean_object* v___x_201_; 
lean_dec(v_h__1_195_);
v_p_199_ = lean_ctor_get(v_x_194_, 0);
lean_inc_ref(v_p_199_);
v_m_200_ = lean_ctor_get(v_x_194_, 1);
lean_inc(v_m_200_);
lean_dec_ref_known(v_x_194_, 2);
v___x_201_ = lean_apply_2(v_h__2_196_, v_p_199_, v_m_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelInv(lean_object* v_x_202_, lean_object* v_y_203_, lean_object* v_m_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_eq(v_x_202_, v_y_203_);
if (v___x_205_ == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_a_206_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_204_, v_x_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v_a_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v_b_209_; uint8_t v___x_210_; 
v_b_209_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_204_, v_y_203_);
v___x_210_ = lean_nat_dec_eq(v_b_209_, v___x_207_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v_m_x27_212_; uint8_t v___x_213_; 
v___x_211_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_204_, v_x_202_);
v_m_x27_212_ = l_Lean_Grind_CommRing_Mon_cancelVar(v___x_211_, v_y_203_);
v___x_213_ = lean_nat_dec_lt(v_a_206_, v_b_209_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
lean_dec(v_y_203_);
v___x_214_ = lean_nat_dec_lt(v_b_209_, v_a_206_);
if (v___x_214_ == 0)
{
lean_dec(v_b_209_);
lean_dec(v_a_206_);
lean_dec(v_x_202_);
return v_m_x27_212_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_nat_sub(v_a_206_, v_b_209_);
lean_dec(v_b_209_);
lean_dec(v_a_206_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_x_202_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_216_, v_m_x27_212_);
return v___x_217_;
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_x_202_);
v___x_218_ = lean_nat_sub(v_b_209_, v_a_206_);
lean_dec(v_a_206_);
lean_dec(v_b_209_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_y_203_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_219_, v_m_x27_212_);
return v___x_220_;
}
}
else
{
lean_dec(v_b_209_);
lean_dec(v_a_206_);
lean_dec(v_y_203_);
lean_dec(v_x_202_);
return v_m_204_;
}
}
else
{
lean_dec(v_a_206_);
lean_dec(v_y_203_);
lean_dec(v_x_202_);
return v_m_204_;
}
}
else
{
lean_dec(v_y_203_);
lean_dec(v_x_202_);
return v_m_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv_go(lean_object* v_x_221_, lean_object* v_y_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
if (lean_obj_tag(v_a_223_) == 0)
{
lean_object* v_k_225_; lean_object* v___x_226_; 
lean_dec(v_y_222_);
lean_dec(v_x_221_);
v_k_225_ = lean_ctor_get(v_a_223_, 0);
lean_inc(v_k_225_);
lean_dec_ref_known(v_a_223_, 1);
v___x_226_ = l_Lean_Grind_CommRing_Poly_addConst(v_a_224_, v_k_225_);
lean_dec(v_k_225_);
return v___x_226_;
}
else
{
lean_object* v_k_227_; lean_object* v_v_228_; lean_object* v_p_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_k_227_ = lean_ctor_get(v_a_223_, 0);
lean_inc(v_k_227_);
v_v_228_ = lean_ctor_get(v_a_223_, 1);
lean_inc(v_v_228_);
v_p_229_ = lean_ctor_get(v_a_223_, 2);
lean_inc_ref(v_p_229_);
lean_dec_ref_known(v_a_223_, 3);
lean_inc(v_y_222_);
lean_inc(v_x_221_);
v___x_230_ = l_Lean_Grind_CommRing_Mon_cancelInv(v_x_221_, v_y_222_, v_v_228_);
v___x_231_ = l_Lean_Grind_CommRing_Poly_insert(v_k_227_, v___x_230_, v_a_224_);
v_a_223_ = v_p_229_;
v_a_224_ = v___x_231_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_nat_to_int(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__0, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv(lean_object* v_x_237_, lean_object* v_y_238_, lean_object* v_p_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__1, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1);
v___x_241_ = l_Lean_Grind_CommRing_Poly_cancelInv_go(v_x_237_, v_y_238_, v_p_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Poly_cancelInv_go_match__1_splitter___redArg(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v_k_246_; lean_object* v___x_247_; 
lean_dec(v_h__2_245_);
v_k_246_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_k_246_);
lean_dec_ref_known(v_x_242_, 1);
v___x_247_ = lean_apply_2(v_h__1_244_, v_k_246_, v_x_243_);
return v___x_247_;
}
else
{
lean_object* v_k_248_; lean_object* v_v_249_; lean_object* v_p_250_; lean_object* v___x_251_; 
lean_dec(v_h__1_244_);
v_k_248_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_k_248_);
v_v_249_ = lean_ctor_get(v_x_242_, 1);
lean_inc(v_v_249_);
v_p_250_ = lean_ctor_get(v_x_242_, 2);
lean_inc_ref(v_p_250_);
lean_dec_ref_known(v_x_242_, 3);
v___x_251_ = lean_apply_4(v_h__2_245_, v_k_248_, v_v_249_, v_p_250_, v_x_243_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_FieldSolver_0__Lean_Grind_CommRing_Poly_cancelInv_go_match__1_splitter(lean_object* v_motive_252_, lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_h__1_255_, lean_object* v_h__2_256_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v_k_257_; lean_object* v___x_258_; 
lean_dec(v_h__2_256_);
v_k_257_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_k_257_);
lean_dec_ref_known(v_x_253_, 1);
v___x_258_ = lean_apply_2(v_h__1_255_, v_k_257_, v_x_254_);
return v___x_258_;
}
else
{
lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_p_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_255_);
v_k_259_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_k_259_);
v_v_260_ = lean_ctor_get(v_x_253_, 1);
lean_inc(v_v_260_);
v_p_261_ = lean_ctor_get(v_x_253_, 2);
lean_inc_ref(v_p_261_);
lean_dec_ref_known(v_x_253_, 3);
v___x_262_ = lean_apply_4(v_h__2_256_, v_k_259_, v_v_260_, v_p_261_, v_x_254_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
return v_x_263_;
}
else
{
lean_object* v_head_265_; lean_object* v_tail_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v___x_269_; 
v_head_265_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_head_265_);
v_tail_266_ = lean_ctor_get(v_x_264_, 1);
lean_inc(v_tail_266_);
lean_dec_ref_known(v_x_264_, 2);
v_fst_267_ = lean_ctor_get(v_head_265_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v_head_265_, 1);
lean_inc(v_snd_268_);
lean_dec(v_head_265_);
v___x_269_ = l_Lean_Grind_CommRing_Poly_cancelInv(v_snd_268_, v_fst_267_, v_x_263_);
v_x_263_ = v___x_269_;
v_x_264_ = v_tail_266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInvs(lean_object* v_p_271_, lean_object* v_ainvs_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_271_, v_ainvs_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg(lean_object* v_inst_274_, lean_object* v_ctx_275_, lean_object* v_q_276_){
_start:
{
lean_object* v_toCommRing_277_; lean_object* v_toSemiring_278_; lean_object* v_toInv_279_; lean_object* v_toMul_280_; lean_object* v_natCast_281_; lean_object* v_num_282_; lean_object* v_den_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_toCommRing_277_ = lean_ctor_get(v_inst_274_, 0);
lean_inc_ref(v_toCommRing_277_);
v_toSemiring_278_ = lean_ctor_get(v_toCommRing_277_, 0);
v_toInv_279_ = lean_ctor_get(v_inst_274_, 1);
lean_inc(v_toInv_279_);
lean_dec_ref(v_inst_274_);
v_toMul_280_ = lean_ctor_get(v_toSemiring_278_, 1);
lean_inc(v_toMul_280_);
v_natCast_281_ = lean_ctor_get(v_toSemiring_278_, 2);
lean_inc(v_natCast_281_);
v_num_282_ = lean_ctor_get(v_q_276_, 0);
lean_inc_ref(v_num_282_);
v_den_283_ = lean_ctor_get(v_q_276_, 1);
lean_inc(v_den_283_);
lean_dec_ref(v_q_276_);
v___x_284_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_toCommRing_277_, v_ctx_275_, v_num_282_);
v___x_285_ = lean_apply_1(v_natCast_281_, v_den_283_);
v___x_286_ = lean_apply_1(v_toInv_279_, v___x_285_);
v___x_287_ = lean_apply_2(v_toMul_280_, v___x_284_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg___boxed(lean_object* v_inst_288_, lean_object* v_ctx_289_, lean_object* v_q_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_288_, v_ctx_289_, v_q_290_);
lean_dec_ref(v_ctx_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_ctx_294_, lean_object* v_q_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_293_, v_ctx_294_, v_q_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___boxed(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_ctx_299_, lean_object* v_q_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Grind_CommRing_PolyQ_denote(v_00_u03b1_297_, v_inst_298_, v_ctx_299_, v_q_300_);
lean_dec_ref(v_ctx_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv(lean_object* v_p_302_, lean_object* v_x_303_, lean_object* v_c_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_nat_dec_eq(v_c_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v_n_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_n_307_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_302_, v_x_303_);
lean_inc(v_c_304_);
v___x_308_ = lean_nat_to_int(v_c_304_);
v___x_309_ = lean_nat_pow(v_c_304_, v_n_307_);
lean_dec(v_n_307_);
lean_dec(v_c_304_);
lean_inc(v___x_309_);
v___x_310_ = lean_nat_to_int(v___x_309_);
v___x_311_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_310_, v_p_302_);
lean_dec(v___x_310_);
v___x_312_ = l_Lean_Grind_CommRing_Poly_cancelVar(v___x_308_, v_x_303_, v___x_311_);
lean_dec(v___x_308_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_309_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_c_304_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_p_302_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv___boxed(lean_object* v_p_316_, lean_object* v_x_317_, lean_object* v_c_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Grind_CommRing_Poly_substInv(v_p_316_, v_x_317_, v_c_318_);
lean_dec(v_x_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv(lean_object* v_q_320_, lean_object* v_x_321_, lean_object* v_c_322_){
_start:
{
lean_object* v_num_323_; lean_object* v_den_324_; lean_object* v_q_x27_325_; lean_object* v_num_326_; lean_object* v_den_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_num_323_ = lean_ctor_get(v_q_320_, 0);
lean_inc_ref(v_num_323_);
v_den_324_ = lean_ctor_get(v_q_320_, 1);
lean_inc(v_den_324_);
lean_dec_ref(v_q_320_);
v_q_x27_325_ = l_Lean_Grind_CommRing_Poly_substInv(v_num_323_, v_x_321_, v_c_322_);
v_num_326_ = lean_ctor_get(v_q_x27_325_, 0);
v_den_327_ = lean_ctor_get(v_q_x27_325_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_q_x27_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v_q_x27_325_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_den_327_);
lean_inc(v_num_326_);
lean_dec(v_q_x27_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_nat_mul(v_den_324_, v_den_327_);
lean_dec(v_den_327_);
lean_dec(v_den_324_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_num_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv___boxed(lean_object* v_q_336_, lean_object* v_x_337_, lean_object* v_c_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_q_336_, v_x_337_, v_c_338_);
lean_dec(v_x_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_reduce(lean_object* v_q_340_){
_start:
{
lean_object* v_num_341_; lean_object* v_den_342_; lean_object* v___x_343_; lean_object* v_g_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_num_341_ = lean_ctor_get(v_q_340_, 0);
v_den_342_ = lean_ctor_get(v_q_340_, 1);
v___x_343_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_num_341_);
v_g_344_ = lean_nat_gcd(v___x_343_, v_den_342_);
lean_dec(v___x_343_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_dec_le(v_g_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v_num_348_; lean_object* v_den_349_; uint8_t v___y_351_; lean_object* v___x_361_; uint8_t v___x_362_; 
lean_inc(v_g_344_);
v___x_347_ = lean_nat_to_int(v_g_344_);
lean_inc_ref(v_num_341_);
v_num_348_ = l_Lean_Grind_CommRing_Poly_divConst(v_num_341_, v___x_347_);
v_den_349_ = lean_nat_div(v_den_342_, v_g_344_);
lean_inc_ref(v_num_348_);
v___x_361_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_347_, v_num_348_);
lean_dec(v___x_347_);
v___x_362_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_361_, v_num_341_);
lean_dec_ref(v___x_361_);
if (v___x_362_ == 0)
{
lean_dec(v_g_344_);
v___y_351_ = v___x_362_;
goto v___jp_350_;
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_nat_mul(v_den_349_, v_g_344_);
lean_dec(v_g_344_);
v___x_364_ = lean_nat_dec_eq(v___x_363_, v_den_342_);
lean_dec(v___x_363_);
v___y_351_ = v___x_364_;
goto v___jp_350_;
}
v___jp_350_:
{
if (v___y_351_ == 0)
{
lean_dec(v_den_349_);
lean_dec_ref(v_num_348_);
return v_q_340_;
}
else
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_isSharedCheck_358_ = !lean_is_exclusive(v_q_340_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_359_ = lean_ctor_get(v_q_340_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_q_340_, 0);
lean_dec(v_unused_360_);
v___x_353_ = v_q_340_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_q_340_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_den_349_);
lean_ctor_set(v___x_353_, 0, v_num_348_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_num_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_den_349_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_dec(v_g_344_);
return v_q_340_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
return v_x_365_;
}
else
{
lean_object* v_head_367_; lean_object* v_tail_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; 
v_head_367_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_head_367_);
v_tail_368_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_tail_368_);
lean_dec_ref_known(v_x_366_, 2);
v_fst_369_ = lean_ctor_get(v_head_367_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v_head_367_, 1);
lean_inc(v_snd_370_);
lean_dec(v_head_367_);
v___x_371_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_x_365_, v_fst_369_, v_snd_370_);
lean_dec(v_fst_369_);
v_x_365_ = v___x_371_;
v_x_366_ = v_tail_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toPolyQ(lean_object* v_p_373_, lean_object* v_invs_374_, lean_object* v_ainvs_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_376_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_373_, v_ainvs_375_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(v___x_378_, v_invs_374_);
v___x_380_ = l_Lean_Grind_CommRing_PolyQ_reduce(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ(lean_object* v_e_381_, lean_object* v_invs_382_, lean_object* v_ainvs_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_Grind_CommRing_Expr_toPoly(v_e_381_);
v___x_385_ = l_Lean_Grind_CommRing_Poly_toPolyQ(v___x_384_, v_invs_382_, v_ainvs_383_);
return v___x_385_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_cancelInvs__cert(lean_object* v_ainvs_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_389_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_387_);
lean_inc(v_ainvs_386_);
v___x_390_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_389_, v_ainvs_386_);
v___x_391_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_388_);
v___x_392_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_391_, v_ainvs_386_);
v___x_393_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_390_, v___x_392_);
lean_dec_ref(v___x_392_);
lean_dec_ref(v___x_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_cancelInvs__cert___boxed(lean_object* v_ainvs_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Lean_Grind_CommRing_Expr_cancelInvs__cert(v_ainvs_394_, v_a_395_, v_b_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normA__cert(lean_object* v_ainvs_399_, lean_object* v_lhs_400_, lean_object* v_rhs_401_, lean_object* v_lhs_x27_402_, lean_object* v_rhs_x27_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_404_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_404_, 0, v_lhs_400_);
lean_ctor_set(v___x_404_, 1, v_rhs_401_);
v___x_405_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_404_);
v___x_406_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_405_, v_ainvs_399_);
v___x_407_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_407_, 0, v_lhs_x27_402_);
lean_ctor_set(v___x_407_, 1, v_rhs_x27_403_);
v___x_408_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_407_);
v___x_409_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_406_, v___x_408_);
lean_dec_ref(v___x_408_);
lean_dec_ref(v___x_406_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normA__cert___boxed(lean_object* v_ainvs_410_, lean_object* v_lhs_411_, lean_object* v_rhs_412_, lean_object* v_lhs_x27_413_, lean_object* v_rhs_x27_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_Grind_CommRing_normA__cert(v_ainvs_410_, v_lhs_411_, v_rhs_412_, v_lhs_x27_413_, v_rhs_x27_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Expr_toPolyQ__cert(lean_object* v_invs_417_, lean_object* v_ainvs_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
lean_inc(v_ainvs_418_);
lean_inc(v_invs_417_);
v___x_421_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_a_419_, v_invs_417_, v_ainvs_418_);
v___x_422_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_b_420_, v_invs_417_, v_ainvs_418_);
v___x_423_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v___x_421_, v___x_422_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ__cert___boxed(lean_object* v_invs_424_, lean_object* v_ainvs_425_, lean_object* v_a_426_, lean_object* v_b_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_Grind_CommRing_Expr_toPolyQ__cert(v_invs_424_, v_ainvs_425_, v_a_426_, v_b_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_normQ__cert(lean_object* v_invs_430_, lean_object* v_ainvs_431_, lean_object* v_lhs_432_, lean_object* v_rhs_433_, lean_object* v_lhs_x27_434_, lean_object* v_rhs_x27_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_num_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
v___x_436_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_436_, 0, v_lhs_432_);
lean_ctor_set(v___x_436_, 1, v_rhs_433_);
v___x_437_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v___x_436_, v_invs_430_, v_ainvs_431_);
v_num_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_437_, 1);
lean_dec(v_unused_448_);
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_num_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 6);
lean_ctor_set(v___x_440_, 1, v_rhs_x27_435_);
lean_ctor_set(v___x_440_, 0, v_lhs_x27_434_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_lhs_x27_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_rhs_x27_435_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_443_);
v___x_445_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_num_438_, v___x_444_);
lean_dec_ref(v___x_444_);
lean_dec_ref(v_num_438_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normQ__cert___boxed(lean_object* v_invs_449_, lean_object* v_ainvs_450_, lean_object* v_lhs_451_, lean_object* v_rhs_452_, lean_object* v_lhs_x27_453_, lean_object* v_rhs_x27_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Lean_Grind_CommRing_normQ__cert(v_invs_449_, v_ainvs_450_, v_lhs_451_, v_rhs_452_, v_lhs_x27_453_, v_rhs_x27_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
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
