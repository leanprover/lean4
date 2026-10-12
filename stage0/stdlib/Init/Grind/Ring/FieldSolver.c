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
uint8_t l_Lean_Grind_CommRing_instBEqPolyQ_beq(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Lean_Grind_CommRing_instBEqPolyQ_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPolyQ_beq___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPolyQ_repr_spec__0(lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_nat_to_int(v_a_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(7u);
v___x_32_ = lean_nat_to_int(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__0));
v___x_41_ = lean_string_length(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__13);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(lean_object* v_x_48_){
_start:
{
lean_object* v_num_49_; lean_object* v_den_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_84_; 
v_num_49_ = lean_ctor_get(v_x_48_, 0);
v_den_50_ = lean_ctor_get(v_x_48_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_84_ == 0)
{
v___x_52_ = v_x_48_;
v_isShared_53_ = v_isSharedCheck_84_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_den_50_);
lean_inc(v_num_49_);
lean_dec(v_x_48_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_84_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_54_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__5));
v___x_55_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__6));
v___x_56_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__7);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_num_49_, v___x_57_);
if (v_isShared_53_ == 0)
{
lean_ctor_set_tag(v___x_52_, 4);
lean_ctor_set(v___x_52_, 1, v___x_58_);
lean_ctor_set(v___x_52_, 0, v___x_56_);
v___x_60_ = v___x_52_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_83_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_61_ = 0;
v___x_62_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_55_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__9));
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_box(1);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__11));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_54_);
v___x_71_ = l_Nat_reprFast(v_den_50_);
v___x_72_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_56_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_61_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__14);
v___x_77_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__15));
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_75_);
v___x_79_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg___closed__16));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_76_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_61_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Grind_CommRing_instReprPolyQ_repr___redArg(v_x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPolyQ_repr___boxed(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Grind_CommRing_instReprPolyQ_repr(v_x_88_, v_prec_89_);
lean_dec(v_prec_89_);
return v_res_90_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPolyQ_default___closed__0);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPolyQ(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Grind_CommRing_instInhabitedPolyQ_default;
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(lean_object* v_ctx_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
if (lean_obj_tag(v_a_99_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = l_List_reverse___redArg(v_a_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_113_; 
v_head_102_ = lean_ctor_get(v_a_99_, 0);
v_tail_103_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_113_ == 0)
{
v___x_105_ = v_a_99_;
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_tail_103_);
lean_inc(v_head_102_);
lean_dec(v_a_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_fst_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v_fst_107_ = lean_ctor_get(v_head_102_, 0);
lean_inc(v_fst_107_);
lean_dec(v_head_102_);
v___x_108_ = l_Lean_RArray_getImpl___redArg(v_ctx_98_, v_fst_107_);
lean_dec(v_fst_107_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_a_100_);
lean_ctor_set(v___x_105_, 0, v___x_108_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_a_100_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v_a_99_ = v_tail_103_;
v_a_100_ = v___x_110_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg___boxed(lean_object* v_ctx_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_114_, v_a_115_, v_a_116_);
lean_dec_ref(v_ctx_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(lean_object* v_ctx_118_, lean_object* v_invs_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_box(0);
v___x_121_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_118_, v_invs_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___redArg___boxed(lean_object* v_ctx_122_, lean_object* v_invs_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_122_, v_invs_123_);
lean_dec_ref(v_ctx_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars(lean_object* v_00_u03b1_125_, lean_object* v_ctx_126_, lean_object* v_invs_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Grind_CommRing_InvVars_denoteVars___redArg(v_ctx_126_, v_invs_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteVars___boxed(lean_object* v_00_u03b1_129_, lean_object* v_ctx_130_, lean_object* v_invs_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Grind_CommRing_InvVars_denoteVars(v_00_u03b1_129_, v_ctx_130_, v_invs_131_);
lean_dec_ref(v_ctx_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(lean_object* v_00_u03b1_133_, lean_object* v_ctx_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___redArg(v_ctx_134_, v_a_135_, v_a_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0___boxed(lean_object* v_00_u03b1_138_, lean_object* v_ctx_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_List_mapTR_loop___at___00Lean_Grind_CommRing_InvVars_denoteVars_spec__0(v_00_u03b1_138_, v_ctx_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_ctx_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0(lean_object* v_toSemiring_143_, lean_object* v_toInv_144_, lean_object* v_p_145_){
_start:
{
lean_object* v_ofNat_146_; lean_object* v_snd_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_ofNat_146_ = lean_ctor_get(v_toSemiring_143_, 3);
lean_inc(v_ofNat_146_);
lean_dec_ref(v_toSemiring_143_);
v_snd_147_ = lean_ctor_get(v_p_145_, 1);
lean_inc(v_snd_147_);
lean_dec_ref(v_p_145_);
v___x_148_ = lean_apply_1(v_ofNat_146_, v_snd_147_);
v___x_149_ = lean_apply_1(v_toInv_144_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(lean_object* v_inst_150_, lean_object* v_invs_151_){
_start:
{
lean_object* v_toCommRing_152_; lean_object* v_toInv_153_; lean_object* v_toSemiring_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_toCommRing_152_ = lean_ctor_get(v_inst_150_, 0);
lean_inc_ref(v_toCommRing_152_);
v_toInv_153_ = lean_ctor_get(v_inst_150_, 1);
lean_inc(v_toInv_153_);
lean_dec_ref(v_inst_150_);
v_toSemiring_154_ = lean_ctor_get(v_toCommRing_152_, 0);
lean_inc_ref(v_toSemiring_154_);
lean_dec_ref(v_toCommRing_152_);
v___f_155_ = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg___lam__0), 3, 2);
lean_closure_set(v___f_155_, 0, v_toSemiring_154_);
lean_closure_set(v___f_155_, 1, v_toInv_153_);
v___x_156_ = lean_box(0);
v___x_157_ = l_List_mapTR_loop___redArg(v___f_155_, v_invs_151_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_InvVars_denoteInvs(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_invs_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Grind_CommRing_InvVars_denoteInvs___redArg(v_inst_159_, v_invs_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelInv(lean_object* v_x_162_, lean_object* v_y_163_, lean_object* v_m_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_eq(v_x_162_, v_y_163_);
if (v___x_165_ == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_a_166_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_164_, v_x_162_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_nat_dec_eq(v_a_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v_b_169_; uint8_t v___x_170_; 
v_b_169_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_164_, v_y_163_);
v___x_170_ = lean_nat_dec_eq(v_b_169_, v___x_167_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v_m_x27_172_; uint8_t v___x_173_; 
v___x_171_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_164_, v_x_162_);
v_m_x27_172_ = l_Lean_Grind_CommRing_Mon_cancelVar(v___x_171_, v_y_163_);
v___x_173_ = lean_nat_dec_lt(v_a_166_, v_b_169_);
if (v___x_173_ == 0)
{
uint8_t v___x_174_; 
lean_dec(v_y_163_);
v___x_174_ = lean_nat_dec_lt(v_b_169_, v_a_166_);
if (v___x_174_ == 0)
{
lean_dec(v_b_169_);
lean_dec(v_a_166_);
lean_dec(v_x_162_);
return v_m_x27_172_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_nat_sub(v_a_166_, v_b_169_);
lean_dec(v_b_169_);
lean_dec(v_a_166_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v_x_162_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_176_, v_m_x27_172_);
return v___x_177_;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_x_162_);
v___x_178_ = lean_nat_sub(v_b_169_, v_a_166_);
lean_dec(v_a_166_);
lean_dec(v_b_169_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_y_163_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_Grind_CommRing_Mon_mulPow(v___x_179_, v_m_x27_172_);
return v___x_180_;
}
}
else
{
lean_dec(v_b_169_);
lean_dec(v_a_166_);
lean_dec(v_y_163_);
lean_dec(v_x_162_);
return v_m_164_;
}
}
else
{
lean_dec(v_a_166_);
lean_dec(v_y_163_);
lean_dec(v_x_162_);
return v_m_164_;
}
}
else
{
lean_dec(v_y_163_);
lean_dec(v_x_162_);
return v_m_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv_go(lean_object* v_x_181_, lean_object* v_y_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
if (lean_obj_tag(v_a_183_) == 0)
{
lean_object* v_k_185_; lean_object* v___x_186_; 
lean_dec(v_y_182_);
lean_dec(v_x_181_);
v_k_185_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_k_185_);
lean_dec_ref_known(v_a_183_, 1);
v___x_186_ = l_Lean_Grind_CommRing_Poly_addConst(v_a_184_, v_k_185_);
lean_dec(v_k_185_);
return v___x_186_;
}
else
{
lean_object* v_k_187_; lean_object* v_v_188_; lean_object* v_p_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_k_187_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_k_187_);
v_v_188_ = lean_ctor_get(v_a_183_, 1);
lean_inc(v_v_188_);
v_p_189_ = lean_ctor_get(v_a_183_, 2);
lean_inc_ref(v_p_189_);
lean_dec_ref_known(v_a_183_, 3);
lean_inc(v_y_182_);
lean_inc(v_x_181_);
v___x_190_ = l_Lean_Grind_CommRing_Mon_cancelInv(v_x_181_, v_y_182_, v_v_188_);
v___x_191_ = l_Lean_Grind_CommRing_Poly_insert(v_k_187_, v___x_190_, v_a_184_);
v_a_183_ = v_p_189_;
v_a_184_ = v___x_191_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__0, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__0);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInv(lean_object* v_x_197_, lean_object* v_y_198_, lean_object* v_p_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_cancelInv___closed__1, &l_Lean_Grind_CommRing_Poly_cancelInv___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_cancelInv___closed__1);
v___x_201_ = l_Lean_Grind_CommRing_Poly_cancelInv_go(v_x_197_, v_y_198_, v_p_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
return v_x_202_;
}
else
{
lean_object* v_head_204_; lean_object* v_tail_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_208_; 
v_head_204_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_head_204_);
v_tail_205_ = lean_ctor_get(v_x_203_, 1);
lean_inc(v_tail_205_);
lean_dec_ref_known(v_x_203_, 2);
v_fst_206_ = lean_ctor_get(v_head_204_, 0);
lean_inc(v_fst_206_);
v_snd_207_ = lean_ctor_get(v_head_204_, 1);
lean_inc(v_snd_207_);
lean_dec(v_head_204_);
v___x_208_ = l_Lean_Grind_CommRing_Poly_cancelInv(v_snd_207_, v_fst_206_, v_x_202_);
v_x_202_ = v___x_208_;
v_x_203_ = v_tail_205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelInvs(lean_object* v_p_210_, lean_object* v_ainvs_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_210_, v_ainvs_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg(lean_object* v_inst_213_, lean_object* v_ctx_214_, lean_object* v_q_215_){
_start:
{
lean_object* v_toCommRing_216_; lean_object* v_toSemiring_217_; lean_object* v_toInv_218_; lean_object* v_toMul_219_; lean_object* v_natCast_220_; lean_object* v_num_221_; lean_object* v_den_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_toCommRing_216_ = lean_ctor_get(v_inst_213_, 0);
lean_inc_ref(v_toCommRing_216_);
v_toSemiring_217_ = lean_ctor_get(v_toCommRing_216_, 0);
v_toInv_218_ = lean_ctor_get(v_inst_213_, 1);
lean_inc(v_toInv_218_);
lean_dec_ref(v_inst_213_);
v_toMul_219_ = lean_ctor_get(v_toSemiring_217_, 1);
lean_inc(v_toMul_219_);
v_natCast_220_ = lean_ctor_get(v_toSemiring_217_, 2);
lean_inc(v_natCast_220_);
v_num_221_ = lean_ctor_get(v_q_215_, 0);
lean_inc_ref(v_num_221_);
v_den_222_ = lean_ctor_get(v_q_215_, 1);
lean_inc(v_den_222_);
lean_dec_ref(v_q_215_);
v___x_223_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_toCommRing_216_, v_ctx_214_, v_num_221_);
v___x_224_ = lean_apply_1(v_natCast_220_, v_den_222_);
v___x_225_ = lean_apply_1(v_toInv_218_, v___x_224_);
v___x_226_ = lean_apply_2(v_toMul_219_, v___x_223_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___redArg___boxed(lean_object* v_inst_227_, lean_object* v_ctx_228_, lean_object* v_q_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_227_, v_ctx_228_, v_q_229_);
lean_dec_ref(v_ctx_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_ctx_233_, lean_object* v_q_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Grind_CommRing_PolyQ_denote___redArg(v_inst_232_, v_ctx_233_, v_q_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_denote___boxed(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_, lean_object* v_ctx_238_, lean_object* v_q_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Grind_CommRing_PolyQ_denote(v_00_u03b1_236_, v_inst_237_, v_ctx_238_, v_q_239_);
lean_dec_ref(v_ctx_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv(lean_object* v_p_241_, lean_object* v_x_242_, lean_object* v_c_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v_c_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v_n_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_n_246_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_241_, v_x_242_);
lean_inc(v_c_243_);
v___x_247_ = lean_nat_to_int(v_c_243_);
v___x_248_ = lean_nat_pow(v_c_243_, v_n_246_);
lean_dec(v_n_246_);
lean_dec(v_c_243_);
lean_inc(v___x_248_);
v___x_249_ = lean_nat_to_int(v___x_248_);
v___x_250_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_249_, v_p_241_);
lean_dec(v___x_249_);
v___x_251_ = l_Lean_Grind_CommRing_Poly_cancelVar(v___x_247_, v_x_242_, v___x_250_);
lean_dec(v___x_247_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_248_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_c_243_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_p_241_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_substInv___boxed(lean_object* v_p_255_, lean_object* v_x_256_, lean_object* v_c_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Grind_CommRing_Poly_substInv(v_p_255_, v_x_256_, v_c_257_);
lean_dec(v_x_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv(lean_object* v_q_259_, lean_object* v_x_260_, lean_object* v_c_261_){
_start:
{
lean_object* v_num_262_; lean_object* v_den_263_; lean_object* v_q_x27_264_; lean_object* v_num_265_; lean_object* v_den_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_num_262_ = lean_ctor_get(v_q_259_, 0);
lean_inc_ref(v_num_262_);
v_den_263_ = lean_ctor_get(v_q_259_, 1);
lean_inc(v_den_263_);
lean_dec_ref(v_q_259_);
v_q_x27_264_ = l_Lean_Grind_CommRing_Poly_substInv(v_num_262_, v_x_260_, v_c_261_);
v_num_265_ = lean_ctor_get(v_q_x27_264_, 0);
v_den_266_ = lean_ctor_get(v_q_x27_264_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_q_x27_264_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_q_x27_264_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_den_266_);
lean_inc(v_num_265_);
lean_dec(v_q_x27_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_nat_mul(v_den_263_, v_den_266_);
lean_dec(v_den_266_);
lean_dec(v_den_263_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_num_265_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_substInv___boxed(lean_object* v_q_275_, lean_object* v_x_276_, lean_object* v_c_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_q_275_, v_x_276_, v_c_277_);
lean_dec(v_x_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PolyQ_reduce(lean_object* v_q_279_){
_start:
{
lean_object* v_num_280_; lean_object* v_den_281_; lean_object* v___x_282_; lean_object* v_g_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_num_280_ = lean_ctor_get(v_q_279_, 0);
v_den_281_ = lean_ctor_get(v_q_279_, 1);
v___x_282_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_num_280_);
v_g_283_ = lean_nat_gcd(v___x_282_, v_den_281_);
lean_dec(v___x_282_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_dec_le(v_g_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v_num_287_; lean_object* v_den_288_; uint8_t v___y_290_; lean_object* v___x_300_; uint8_t v___x_301_; 
lean_inc(v_g_283_);
v___x_286_ = lean_nat_to_int(v_g_283_);
lean_inc_ref(v_num_280_);
v_num_287_ = l_Lean_Grind_CommRing_Poly_divConst(v_num_280_, v___x_286_);
v_den_288_ = lean_nat_div(v_den_281_, v_g_283_);
lean_inc_ref(v_num_287_);
v___x_300_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_286_, v_num_287_);
lean_dec(v___x_286_);
v___x_301_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_300_, v_num_280_);
lean_dec_ref(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_g_283_);
v___y_290_ = v___x_301_;
goto v___jp_289_;
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_nat_mul(v_den_288_, v_g_283_);
lean_dec(v_g_283_);
v___x_303_ = lean_nat_dec_eq(v___x_302_, v_den_281_);
lean_dec(v___x_302_);
v___y_290_ = v___x_303_;
goto v___jp_289_;
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
lean_dec(v_den_288_);
lean_dec_ref(v_num_287_);
return v_q_279_;
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v_q_279_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_q_279_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_q_279_, 0);
lean_dec(v_unused_299_);
v___x_292_ = v_q_279_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_dec(v_q_279_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_den_288_);
lean_ctor_set(v___x_292_, 0, v_num_287_);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_num_287_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_den_288_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
else
{
lean_dec(v_g_283_);
return v_q_279_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
return v_x_304_;
}
else
{
lean_object* v_head_306_; lean_object* v_tail_307_; lean_object* v_fst_308_; lean_object* v_snd_309_; lean_object* v___x_310_; 
v_head_306_ = lean_ctor_get(v_x_305_, 0);
lean_inc(v_head_306_);
v_tail_307_ = lean_ctor_get(v_x_305_, 1);
lean_inc(v_tail_307_);
lean_dec_ref_known(v_x_305_, 2);
v_fst_308_ = lean_ctor_get(v_head_306_, 0);
lean_inc(v_fst_308_);
v_snd_309_ = lean_ctor_get(v_head_306_, 1);
lean_inc(v_snd_309_);
lean_dec(v_head_306_);
v___x_310_ = l_Lean_Grind_CommRing_PolyQ_substInv(v_x_304_, v_fst_308_, v_snd_309_);
lean_dec(v_fst_308_);
v_x_304_ = v___x_310_;
v_x_305_ = v_tail_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toPolyQ(lean_object* v_p_312_, lean_object* v_invs_313_, lean_object* v_ainvs_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_315_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v_p_312_, v_ainvs_314_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_toPolyQ_spec__0(v___x_317_, v_invs_313_);
v___x_319_ = l_Lean_Grind_CommRing_PolyQ_reduce(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ(lean_object* v_e_320_, lean_object* v_invs_321_, lean_object* v_ainvs_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l_Lean_Grind_CommRing_Expr_toPoly(v_e_320_);
v___x_324_ = l_Lean_Grind_CommRing_Poly_toPolyQ(v___x_323_, v_invs_321_, v_ainvs_322_);
return v___x_324_;
}
}
uint8_t l_Lean_Grind_CommRing_Expr_cancelInvs__cert(lean_object* v_ainvs_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_328_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_326_);
lean_inc(v_ainvs_325_);
v___x_329_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_328_, v_ainvs_325_);
v___x_330_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_327_);
v___x_331_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_330_, v_ainvs_325_);
v___x_332_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
lean_dec_ref(v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Expr_cancelInvs__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_ainvs_325_ = stack[0].m_obj;
lean_object* v_a_326_ = stack[1].m_obj;
lean_object* v_b_327_ = stack[2].m_obj;
uint8_t v_res_333_;
v_res_333_ = l_Lean_Grind_CommRing_Expr_cancelInvs__cert(v_ainvs_325_, v_a_326_, v_b_327_);
stack->m_num = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_cancelInvs__cert___boxed(lean_object* v_ainvs_334_, lean_object* v_a_335_, lean_object* v_b_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_Grind_CommRing_Expr_cancelInvs__cert(v_ainvs_334_, v_a_335_, v_b_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
uint8_t l_Lean_Grind_CommRing_normA__cert(lean_object* v_ainvs_339_, lean_object* v_lhs_340_, lean_object* v_rhs_341_, lean_object* v_lhs_x27_342_, lean_object* v_rhs_x27_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_344_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_344_, 0, v_lhs_340_);
lean_ctor_set(v___x_344_, 1, v_rhs_341_);
v___x_345_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_344_);
v___x_346_ = l_List_foldl___at___00Lean_Grind_CommRing_Poly_cancelInvs_spec__0(v___x_345_, v_ainvs_339_);
v___x_347_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_347_, 0, v_lhs_x27_342_);
lean_ctor_set(v___x_347_, 1, v_rhs_x27_343_);
v___x_348_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_347_);
v___x_349_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_346_, v___x_348_);
lean_dec_ref(v___x_348_);
lean_dec_ref(v___x_346_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_normA__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_ainvs_339_ = stack[0].m_obj;
lean_object* v_lhs_340_ = stack[1].m_obj;
lean_object* v_rhs_341_ = stack[2].m_obj;
lean_object* v_lhs_x27_342_ = stack[3].m_obj;
lean_object* v_rhs_x27_343_ = stack[4].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_Lean_Grind_CommRing_normA__cert(v_ainvs_339_, v_lhs_340_, v_rhs_341_, v_lhs_x27_342_, v_rhs_x27_343_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normA__cert___boxed(lean_object* v_ainvs_351_, lean_object* v_lhs_352_, lean_object* v_rhs_353_, lean_object* v_lhs_x27_354_, lean_object* v_rhs_x27_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lean_Grind_CommRing_normA__cert(v_ainvs_351_, v_lhs_352_, v_rhs_353_, v_lhs_x27_354_, v_rhs_x27_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
uint8_t l_Lean_Grind_CommRing_Expr_toPolyQ__cert(lean_object* v_invs_358_, lean_object* v_ainvs_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
lean_inc(v_ainvs_359_);
lean_inc(v_invs_358_);
v___x_362_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_a_360_, v_invs_358_, v_ainvs_359_);
v___x_363_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v_b_361_, v_invs_358_, v_ainvs_359_);
v___x_364_ = l_Lean_Grind_CommRing_instBEqPolyQ_beq(v___x_362_, v___x_363_);
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_362_);
return v___x_364_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Expr_toPolyQ__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_invs_358_ = stack[0].m_obj;
lean_object* v_ainvs_359_ = stack[1].m_obj;
lean_object* v_a_360_ = stack[2].m_obj;
lean_object* v_b_361_ = stack[3].m_obj;
uint8_t v_res_365_;
v_res_365_ = l_Lean_Grind_CommRing_Expr_toPolyQ__cert(v_invs_358_, v_ainvs_359_, v_a_360_, v_b_361_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyQ__cert___boxed(lean_object* v_invs_366_, lean_object* v_ainvs_367_, lean_object* v_a_368_, lean_object* v_b_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_Grind_CommRing_Expr_toPolyQ__cert(v_invs_366_, v_ainvs_367_, v_a_368_, v_b_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
uint8_t l_Lean_Grind_CommRing_normQ__cert(lean_object* v_invs_372_, lean_object* v_ainvs_373_, lean_object* v_lhs_374_, lean_object* v_rhs_375_, lean_object* v_lhs_x27_376_, lean_object* v_rhs_x27_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_num_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v___x_378_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_378_, 0, v_lhs_374_);
lean_ctor_set(v___x_378_, 1, v_rhs_375_);
v___x_379_ = l_Lean_Grind_CommRing_Expr_toPolyQ(v___x_378_, v_invs_372_, v_ainvs_373_);
v_num_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v___x_379_, 1);
lean_dec(v_unused_390_);
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_num_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 6);
lean_ctor_set(v___x_382_, 1, v_rhs_x27_377_);
lean_ctor_set(v___x_382_, 0, v_lhs_x27_376_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_lhs_x27_376_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_rhs_x27_377_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_385_);
v___x_387_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_num_380_, v___x_386_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v_num_380_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_normQ__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_invs_372_ = stack[0].m_obj;
lean_object* v_ainvs_373_ = stack[1].m_obj;
lean_object* v_lhs_374_ = stack[2].m_obj;
lean_object* v_rhs_375_ = stack[3].m_obj;
lean_object* v_lhs_x27_376_ = stack[4].m_obj;
lean_object* v_rhs_x27_377_ = stack[5].m_obj;
uint8_t v_res_391_;
v_res_391_ = l_Lean_Grind_CommRing_normQ__cert(v_invs_372_, v_ainvs_373_, v_lhs_374_, v_rhs_375_, v_lhs_x27_376_, v_rhs_x27_377_);
stack->m_num = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_normQ__cert___boxed(lean_object* v_invs_392_, lean_object* v_ainvs_393_, lean_object* v_lhs_394_, lean_object* v_rhs_395_, lean_object* v_lhs_x27_396_, lean_object* v_rhs_x27_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_Grind_CommRing_normQ__cert(v_invs_392_, v_ainvs_393_, v_lhs_394_, v_rhs_395_, v_lhs_x27_396_, v_rhs_x27_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
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
