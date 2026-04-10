// Lean compiler output
// Module: Lean.Meta.Sym.Arith.DenoteExpr
// Imports: public import Lean.Meta.Sym.Arith.Functions public import Lean.Meta.Sym.Arith.MonadVar
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__0(lean_object* v_e_1_, lean_object* v_toPure_2_, lean_object* v_____do__lift_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Expr_app___override(v_____do__lift_3_, v_e_1_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1(lean_object* v___x_9_, lean_object* v___x_10_, lean_object* v_type_11_, lean_object* v_n_12_, lean_object* v_k_13_, lean_object* v_toPure_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_toBind_20_, lean_object* v_ofNatInst_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_e_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_22_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__0));
v___x_23_ = l_Lean_Name_mkStr2(v___x_9_, v___x_22_);
v___x_24_ = l_Lean_mkConst(v___x_23_, v___x_10_);
v_e_25_ = l_Lean_mkApp3(v___x_24_, v_type_11_, v_n_12_, v_ofNatInst_21_);
v___x_26_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1);
v___x_27_ = lean_int_dec_lt(v_k_13_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec(v_toBind_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
lean_dec(v_inst_15_);
v___x_28_ = lean_apply_2(v_toPure_14_, lean_box(0), v_e_25_);
return v___x_28_;
}
else
{
lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v_e_25_);
lean_closure_set(v___f_29_, 1, v_toPure_14_);
v___x_30_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_);
v___x_31_ = lean_apply_4(v_toBind_20_, lean_box(0), lean_box(0), v___x_30_, v___f_29_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___boxed(lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_type_34_, lean_object* v_n_35_, lean_object* v_k_36_, lean_object* v_toPure_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_toBind_43_, lean_object* v_ofNatInst_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1(v___x_32_, v___x_33_, v_type_34_, v_n_35_, v_k_36_, v_toPure_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_toBind_43_, v_ofNatInst_44_);
lean_dec(v_k_36_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__2(lean_object* v___f_46_, lean_object* v_ofNatInst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_apply_1(v___f_46_, v_ofNatInst_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4(lean_object* v_toPure_57_, lean_object* v_toBind_58_, lean_object* v___f_59_, lean_object* v___x_60_, lean_object* v_type_61_, lean_object* v_semiringInst_62_, lean_object* v_n_63_, lean_object* v___f_64_, lean_object* v_____do__lift_65_){
_start:
{
if (lean_obj_tag(v_____do__lift_65_) == 1)
{
lean_object* v_val_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v___f_64_);
lean_dec_ref(v_n_63_);
lean_dec_ref(v_semiringInst_62_);
lean_dec_ref(v_type_61_);
lean_dec(v___x_60_);
v_val_66_ = lean_ctor_get(v_____do__lift_65_, 0);
lean_inc(v_val_66_);
lean_dec_ref(v_____do__lift_65_);
v___x_67_ = lean_apply_2(v_toPure_57_, lean_box(0), v_val_66_);
v___x_68_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_67_, v___f_59_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_____do__lift_65_);
lean_dec(v___f_59_);
v___x_69_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4___closed__3));
v___x_70_ = l_Lean_mkConst(v___x_69_, v___x_60_);
v___x_71_ = l_Lean_mkApp3(v___x_70_, v_type_61_, v_semiringInst_62_, v_n_63_);
v___x_72_ = lean_apply_2(v_toPure_57_, lean_box(0), v___x_71_);
v___x_73_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_72_, v___f_64_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3(lean_object* v_inst_77_, lean_object* v_k_78_, lean_object* v_toPure_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_toBind_84_, lean_object* v_ring_85_){
_start:
{
lean_object* v_synthInstance_x3f_86_; lean_object* v_type_87_; lean_object* v_u_88_; lean_object* v_semiringInst_89_; lean_object* v___x_90_; lean_object* v_n_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_synthInstance_x3f_86_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_synthInstance_x3f_86_);
v_type_87_ = lean_ctor_get(v_ring_85_, 1);
lean_inc_ref_n(v_type_87_, 3);
v_u_88_ = lean_ctor_get(v_ring_85_, 2);
lean_inc(v_u_88_);
v_semiringInst_89_ = lean_ctor_get(v_ring_85_, 4);
lean_inc_ref(v_semiringInst_89_);
lean_dec_ref(v_ring_85_);
v___x_90_ = lean_nat_abs(v_k_78_);
v_n_91_ = l_Lean_mkRawNatLit(v___x_90_);
v___x_92_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__0));
v___x_93_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3___closed__1));
v___x_94_ = lean_box(0);
v___x_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_95_, 0, v_u_88_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
lean_inc_n(v_toBind_84_, 2);
lean_inc(v_toPure_79_);
lean_inc_ref_n(v_n_91_, 2);
lean_inc_ref_n(v___x_95_, 2);
v___f_96_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_96_, 0, v___x_92_);
lean_closure_set(v___f_96_, 1, v___x_95_);
lean_closure_set(v___f_96_, 2, v_type_87_);
lean_closure_set(v___f_96_, 3, v_n_91_);
lean_closure_set(v___f_96_, 4, v_k_78_);
lean_closure_set(v___f_96_, 5, v_toPure_79_);
lean_closure_set(v___f_96_, 6, v_inst_80_);
lean_closure_set(v___f_96_, 7, v_inst_81_);
lean_closure_set(v___f_96_, 8, v_inst_82_);
lean_closure_set(v___f_96_, 9, v_inst_77_);
lean_closure_set(v___f_96_, 10, v_inst_83_);
lean_closure_set(v___f_96_, 11, v_toBind_84_);
v___f_97_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__2), 2, 1);
lean_closure_set(v___f_97_, 0, v___f_96_);
lean_inc_ref(v___f_97_);
v___f_98_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__4), 9, 8);
lean_closure_set(v___f_98_, 0, v_toPure_79_);
lean_closure_set(v___f_98_, 1, v_toBind_84_);
lean_closure_set(v___f_98_, 2, v___f_97_);
lean_closure_set(v___f_98_, 3, v___x_95_);
lean_closure_set(v___f_98_, 4, v_type_87_);
lean_closure_set(v___f_98_, 5, v_semiringInst_89_);
lean_closure_set(v___f_98_, 6, v_n_91_);
lean_closure_set(v___f_98_, 7, v___f_97_);
v___x_99_ = l_Lean_mkConst(v___x_93_, v___x_95_);
v___x_100_ = l_Lean_mkAppB(v___x_99_, v_type_87_, v_n_91_);
v___x_101_ = lean_apply_1(v_synthInstance_x3f_86_, v___x_100_);
v___x_102_ = lean_apply_4(v_toBind_84_, lean_box(0), lean_box(0), v___x_101_, v___f_98_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___redArg(lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_k_108_){
_start:
{
lean_object* v_toApplicative_109_; lean_object* v_toBind_110_; lean_object* v_getRing_111_; lean_object* v_toPure_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v_toApplicative_109_ = lean_ctor_get(v_inst_103_, 0);
v_toBind_110_ = lean_ctor_get(v_inst_103_, 1);
lean_inc_n(v_toBind_110_, 2);
v_getRing_111_ = lean_ctor_get(v_inst_107_, 0);
lean_inc(v_getRing_111_);
v_toPure_112_ = lean_ctor_get(v_toApplicative_109_, 1);
lean_inc(v_toPure_112_);
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__3), 9, 8);
lean_closure_set(v___f_113_, 0, v_inst_106_);
lean_closure_set(v___f_113_, 1, v_k_108_);
lean_closure_set(v___f_113_, 2, v_toPure_112_);
lean_closure_set(v___f_113_, 3, v_inst_105_);
lean_closure_set(v___f_113_, 4, v_inst_104_);
lean_closure_set(v___f_113_, 5, v_inst_103_);
lean_closure_set(v___f_113_, 6, v_inst_107_);
lean_closure_set(v___f_113_, 7, v_toBind_110_);
v___x_114_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v_getRing_111_, v___f_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum(lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_k_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_116_, v_inst_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_k_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0(lean_object* v_toApplicative_123_, lean_object* v_k_124_, lean_object* v_x_125_, lean_object* v_____do__lift_126_){
_start:
{
lean_object* v_toPure_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_toPure_127_ = lean_ctor_get(v_toApplicative_123_, 1);
lean_inc(v_toPure_127_);
lean_dec_ref(v_toApplicative_123_);
v___x_128_ = l_Lean_mkNatLit(v_k_124_);
v___x_129_ = l_Lean_mkAppB(v_____do__lift_126_, v_x_125_, v___x_128_);
v___x_130_ = lean_apply_2(v_toPure_127_, lean_box(0), v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1(lean_object* v_k_131_, lean_object* v_toApplicative_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_toBind_138_, lean_object* v_x_139_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_dec_eq(v_k_131_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___f_142_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0), 4, 3);
lean_closure_set(v___f_142_, 0, v_toApplicative_132_);
lean_closure_set(v___f_142_, 1, v_k_131_);
lean_closure_set(v___f_142_, 2, v_x_139_);
v___x_143_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_inst_137_);
v___x_144_ = lean_apply_4(v_toBind_138_, lean_box(0), lean_box(0), v___x_143_, v___f_142_);
return v___x_144_;
}
else
{
lean_object* v_toPure_145_; lean_object* v___x_146_; 
lean_dec(v_toBind_138_);
lean_dec_ref(v_inst_137_);
lean_dec_ref(v_inst_136_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
lean_dec(v_inst_133_);
lean_dec(v_k_131_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_145_);
lean_dec_ref(v_toApplicative_132_);
v___x_146_ = lean_apply_2(v_toPure_145_, lean_box(0), v_x_139_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_pw_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toBind_155_; lean_object* v_x_156_; lean_object* v_k_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_ref(v_toApplicative_154_);
v_toBind_155_ = lean_ctor_get(v_inst_147_, 1);
lean_inc_n(v_toBind_155_, 2);
v_x_156_ = lean_ctor_get(v_pw_153_, 0);
lean_inc(v_x_156_);
v_k_157_ = lean_ctor_get(v_pw_153_, 1);
lean_inc(v_k_157_);
lean_dec_ref(v_pw_153_);
v___f_158_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1), 9, 8);
lean_closure_set(v___f_158_, 0, v_k_157_);
lean_closure_set(v___f_158_, 1, v_toApplicative_154_);
lean_closure_set(v___f_158_, 2, v_inst_149_);
lean_closure_set(v___f_158_, 3, v_inst_148_);
lean_closure_set(v___f_158_, 4, v_inst_147_);
lean_closure_set(v___f_158_, 5, v_inst_150_);
lean_closure_set(v___f_158_, 6, v_inst_151_);
lean_closure_set(v___f_158_, 7, v_toBind_155_);
v___x_159_ = lean_apply_1(v_inst_152_, v_x_156_);
v___x_160_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_159_, v___f_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower(lean_object* v_m_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_pw_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_162_, v_inst_163_, v_inst_164_, v_inst_165_, v_inst_166_, v_inst_167_, v_pw_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1(lean_object* v_acc_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_m_177_, lean_object* v_p_178_, lean_object* v_toBind_179_, lean_object* v_____do__lift_180_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc(v_inst_176_);
lean_inc_ref(v_inst_175_);
lean_inc_ref(v_inst_174_);
lean_inc(v_inst_173_);
lean_inc_ref(v_inst_172_);
lean_inc_ref(v_inst_171_);
v___f_181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0), 10, 9);
lean_closure_set(v___f_181_, 0, v_____do__lift_180_);
lean_closure_set(v___f_181_, 1, v_acc_170_);
lean_closure_set(v___f_181_, 2, v_inst_171_);
lean_closure_set(v___f_181_, 3, v_inst_172_);
lean_closure_set(v___f_181_, 4, v_inst_173_);
lean_closure_set(v___f_181_, 5, v_inst_174_);
lean_closure_set(v___f_181_, 6, v_inst_175_);
lean_closure_set(v___f_181_, 7, v_inst_176_);
lean_closure_set(v___f_181_, 8, v_m_177_);
v___x_182_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_171_, v_inst_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_, v_p_178_);
v___x_183_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v___x_182_, v___f_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_mn_190_, lean_object* v_acc_191_){
_start:
{
if (lean_obj_tag(v_mn_190_) == 0)
{
lean_object* v_toApplicative_192_; lean_object* v_toPure_193_; lean_object* v___x_194_; 
v_toApplicative_192_ = lean_ctor_get(v_inst_184_, 0);
lean_inc_ref(v_toApplicative_192_);
lean_dec(v_inst_189_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
lean_dec(v_inst_186_);
lean_dec_ref(v_inst_185_);
lean_dec_ref(v_inst_184_);
v_toPure_193_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_193_);
lean_dec_ref(v_toApplicative_192_);
v___x_194_ = lean_apply_2(v_toPure_193_, lean_box(0), v_acc_191_);
return v___x_194_;
}
else
{
lean_object* v_toBind_195_; lean_object* v_p_196_; lean_object* v_m_197_; lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_toBind_195_ = lean_ctor_get(v_inst_184_, 1);
lean_inc_n(v_toBind_195_, 2);
v_p_196_ = lean_ctor_get(v_mn_190_, 0);
lean_inc_ref(v_p_196_);
v_m_197_ = lean_ctor_get(v_mn_190_, 1);
lean_inc(v_m_197_);
lean_dec_ref(v_mn_190_);
lean_inc_ref(v_inst_188_);
lean_inc_ref(v_inst_187_);
lean_inc(v_inst_186_);
lean_inc_ref(v_inst_185_);
lean_inc_ref(v_inst_184_);
v___f_198_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_198_, 0, v_acc_191_);
lean_closure_set(v___f_198_, 1, v_inst_184_);
lean_closure_set(v___f_198_, 2, v_inst_185_);
lean_closure_set(v___f_198_, 3, v_inst_186_);
lean_closure_set(v___f_198_, 4, v_inst_187_);
lean_closure_set(v___f_198_, 5, v_inst_188_);
lean_closure_set(v___f_198_, 6, v_inst_189_);
lean_closure_set(v___f_198_, 7, v_m_197_);
lean_closure_set(v___f_198_, 8, v_p_196_);
lean_closure_set(v___f_198_, 9, v_toBind_195_);
v___x_199_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_186_, v_inst_185_, v_inst_184_, v_inst_187_, v_inst_188_);
v___x_200_ = lean_apply_4(v_toBind_195_, lean_box(0), lean_box(0), v___x_199_, v___f_198_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0(lean_object* v_____do__lift_201_, lean_object* v_acc_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_m_209_, lean_object* v_____do__lift_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Lean_mkAppB(v_____do__lift_201_, v_acc_202_, v_____do__lift_210_);
v___x_212_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_203_, v_inst_204_, v_inst_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_m_209_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go(lean_object* v_m_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_mn_220_, lean_object* v_acc_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_214_, v_inst_215_, v_inst_216_, v_inst_217_, v_inst_218_, v_inst_219_, v_mn_220_, v_acc_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_m_229_, lean_object* v_____do__lift_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_inst_227_, v_inst_228_, v_m_229_, v_____do__lift_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_mn_240_){
_start:
{
if (lean_obj_tag(v_mn_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_inst_239_);
v___x_241_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0);
v___x_242_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_234_, v_inst_235_, v_inst_236_, v_inst_237_, v_inst_238_, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v_toBind_243_; lean_object* v_p_244_; lean_object* v_m_245_; lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_toBind_243_ = lean_ctor_get(v_inst_234_, 1);
lean_inc(v_toBind_243_);
v_p_244_ = lean_ctor_get(v_mn_240_, 0);
lean_inc_ref(v_p_244_);
v_m_245_ = lean_ctor_get(v_mn_240_, 1);
lean_inc(v_m_245_);
lean_dec_ref(v_mn_240_);
lean_inc(v_inst_239_);
lean_inc_ref(v_inst_238_);
lean_inc_ref(v_inst_237_);
lean_inc(v_inst_236_);
lean_inc_ref(v_inst_235_);
lean_inc_ref(v_inst_234_);
v___f_246_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0), 8, 7);
lean_closure_set(v___f_246_, 0, v_inst_234_);
lean_closure_set(v___f_246_, 1, v_inst_235_);
lean_closure_set(v___f_246_, 2, v_inst_236_);
lean_closure_set(v___f_246_, 3, v_inst_237_);
lean_closure_set(v___f_246_, 4, v_inst_238_);
lean_closure_set(v___f_246_, 5, v_inst_239_);
lean_closure_set(v___f_246_, 6, v_m_245_);
v___x_247_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_234_, v_inst_235_, v_inst_236_, v_inst_237_, v_inst_238_, v_inst_239_, v_p_244_);
v___x_248_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_247_, v___f_246_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon(lean_object* v_m_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_mn_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_250_, v_inst_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_inst_255_, v_mn_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0(lean_object* v_toApplicative_258_, lean_object* v_____do__lift_259_, lean_object* v_____do__lift_260_, lean_object* v_____do__lift_261_){
_start:
{
lean_object* v_toPure_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_toPure_262_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_262_);
lean_dec_ref(v_toApplicative_258_);
v___x_263_ = l_Lean_mkAppB(v_____do__lift_259_, v_____do__lift_260_, v_____do__lift_261_);
v___x_264_ = lean_apply_2(v_toPure_262_, lean_box(0), v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1(lean_object* v_toApplicative_265_, lean_object* v_____do__lift_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_mn_273_, lean_object* v_toBind_274_, lean_object* v_____do__lift_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0), 4, 3);
lean_closure_set(v___f_276_, 0, v_toApplicative_265_);
lean_closure_set(v___f_276_, 1, v_____do__lift_266_);
lean_closure_set(v___f_276_, 2, v_____do__lift_275_);
v___x_277_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_267_, v_inst_268_, v_inst_269_, v_inst_270_, v_inst_271_, v_inst_272_, v_mn_273_);
v___x_278_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_277_, v___f_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2(lean_object* v_toApplicative_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_mn_286_, lean_object* v_toBind_287_, lean_object* v_k_288_, lean_object* v_____do__lift_289_){
_start:
{
lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_inc(v_toBind_287_);
lean_inc_ref(v_inst_284_);
lean_inc_ref(v_inst_283_);
lean_inc(v_inst_282_);
lean_inc_ref(v_inst_281_);
lean_inc_ref(v_inst_280_);
v___f_290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1), 11, 10);
lean_closure_set(v___f_290_, 0, v_toApplicative_279_);
lean_closure_set(v___f_290_, 1, v_____do__lift_289_);
lean_closure_set(v___f_290_, 2, v_inst_280_);
lean_closure_set(v___f_290_, 3, v_inst_281_);
lean_closure_set(v___f_290_, 4, v_inst_282_);
lean_closure_set(v___f_290_, 5, v_inst_283_);
lean_closure_set(v___f_290_, 6, v_inst_284_);
lean_closure_set(v___f_290_, 7, v_inst_285_);
lean_closure_set(v___f_290_, 8, v_mn_286_);
lean_closure_set(v___f_290_, 9, v_toBind_287_);
v___x_291_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_280_, v_inst_281_, v_inst_282_, v_inst_283_, v_inst_284_, v_k_288_);
v___x_292_ = lean_apply_4(v_toBind_287_, lean_box(0), lean_box(0), v___x_291_, v___f_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_k_299_, lean_object* v_mn_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0);
v___x_302_ = lean_int_dec_eq(v_k_299_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v_toApplicative_303_; lean_object* v_toBind_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_toApplicative_303_ = lean_ctor_get(v_inst_293_, 0);
v_toBind_304_ = lean_ctor_get(v_inst_293_, 1);
lean_inc_n(v_toBind_304_, 2);
lean_inc_ref(v_inst_297_);
lean_inc_ref(v_inst_296_);
lean_inc(v_inst_295_);
lean_inc_ref(v_inst_294_);
lean_inc_ref(v_inst_293_);
lean_inc_ref(v_toApplicative_303_);
v___f_305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2), 11, 10);
lean_closure_set(v___f_305_, 0, v_toApplicative_303_);
lean_closure_set(v___f_305_, 1, v_inst_293_);
lean_closure_set(v___f_305_, 2, v_inst_294_);
lean_closure_set(v___f_305_, 3, v_inst_295_);
lean_closure_set(v___f_305_, 4, v_inst_296_);
lean_closure_set(v___f_305_, 5, v_inst_297_);
lean_closure_set(v___f_305_, 6, v_inst_298_);
lean_closure_set(v___f_305_, 7, v_mn_300_);
lean_closure_set(v___f_305_, 8, v_toBind_304_);
lean_closure_set(v___f_305_, 9, v_k_299_);
v___x_306_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_295_, v_inst_294_, v_inst_293_, v_inst_296_, v_inst_297_);
v___x_307_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_306_, v___f_305_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_k_299_);
v___x_308_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_293_, v_inst_294_, v_inst_295_, v_inst_296_, v_inst_297_, v_inst_298_, v_mn_300_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_k_316_, lean_object* v_mn_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_inst_315_, v_k_316_, v_mn_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0(lean_object* v_____do__lift_319_, lean_object* v_acc_320_, lean_object* v_toPure_321_, lean_object* v_____do__lift_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l_Lean_mkAppB(v_____do__lift_319_, v_acc_320_, v_____do__lift_322_);
v___x_324_ = lean_apply_2(v_toPure_321_, lean_box(0), v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1(lean_object* v_acc_325_, lean_object* v_toPure_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_k_332_, lean_object* v_toBind_333_, lean_object* v_____do__lift_334_){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___f_335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0), 4, 3);
lean_closure_set(v___f_335_, 0, v_____do__lift_334_);
lean_closure_set(v___f_335_, 1, v_acc_325_);
lean_closure_set(v___f_335_, 2, v_toPure_326_);
v___x_336_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_327_, v_inst_328_, v_inst_329_, v_inst_330_, v_inst_331_, v_k_332_);
v___x_337_ = lean_apply_4(v_toBind_333_, lean_box(0), lean_box(0), v___x_336_, v___f_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3(lean_object* v_acc_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_p_345_, lean_object* v_k_346_, lean_object* v_v_347_, lean_object* v_toBind_348_, lean_object* v_____do__lift_349_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc(v_inst_344_);
lean_inc_ref(v_inst_343_);
lean_inc_ref(v_inst_342_);
lean_inc(v_inst_341_);
lean_inc_ref(v_inst_340_);
lean_inc_ref(v_inst_339_);
v___f_350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2), 10, 9);
lean_closure_set(v___f_350_, 0, v_____do__lift_349_);
lean_closure_set(v___f_350_, 1, v_acc_338_);
lean_closure_set(v___f_350_, 2, v_inst_339_);
lean_closure_set(v___f_350_, 3, v_inst_340_);
lean_closure_set(v___f_350_, 4, v_inst_341_);
lean_closure_set(v___f_350_, 5, v_inst_342_);
lean_closure_set(v___f_350_, 6, v_inst_343_);
lean_closure_set(v___f_350_, 7, v_inst_344_);
lean_closure_set(v___f_350_, 8, v_p_345_);
v___x_351_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_339_, v_inst_340_, v_inst_341_, v_inst_342_, v_inst_343_, v_inst_344_, v_k_346_, v_v_347_);
v___x_352_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_351_, v___f_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_p_359_, lean_object* v_acc_360_){
_start:
{
if (lean_obj_tag(v_p_359_) == 0)
{
lean_object* v_toApplicative_361_; lean_object* v_toBind_362_; lean_object* v_toPure_363_; lean_object* v_k_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_toApplicative_361_ = lean_ctor_get(v_inst_353_, 0);
lean_dec(v_inst_358_);
v_toBind_362_ = lean_ctor_get(v_inst_353_, 1);
lean_inc(v_toBind_362_);
v_toPure_363_ = lean_ctor_get(v_toApplicative_361_, 1);
v_k_364_ = lean_ctor_get(v_p_359_, 0);
lean_inc(v_k_364_);
lean_dec_ref(v_p_359_);
v___x_365_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1);
v___x_366_ = lean_int_dec_eq(v_k_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_inc(v_toBind_362_);
lean_inc_ref(v_inst_357_);
lean_inc_ref(v_inst_356_);
lean_inc(v_inst_355_);
lean_inc_ref(v_inst_354_);
lean_inc_ref(v_inst_353_);
lean_inc(v_toPure_363_);
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1), 10, 9);
lean_closure_set(v___f_367_, 0, v_acc_360_);
lean_closure_set(v___f_367_, 1, v_toPure_363_);
lean_closure_set(v___f_367_, 2, v_inst_353_);
lean_closure_set(v___f_367_, 3, v_inst_354_);
lean_closure_set(v___f_367_, 4, v_inst_355_);
lean_closure_set(v___f_367_, 5, v_inst_356_);
lean_closure_set(v___f_367_, 6, v_inst_357_);
lean_closure_set(v___f_367_, 7, v_k_364_);
lean_closure_set(v___f_367_, 8, v_toBind_362_);
v___x_368_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_355_, v_inst_354_, v_inst_353_, v_inst_356_, v_inst_357_);
v___x_369_ = lean_apply_4(v_toBind_362_, lean_box(0), lean_box(0), v___x_368_, v___f_367_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
lean_inc(v_toPure_363_);
lean_dec(v_k_364_);
lean_dec(v_toBind_362_);
lean_dec_ref(v_inst_357_);
lean_dec_ref(v_inst_356_);
lean_dec(v_inst_355_);
lean_dec_ref(v_inst_354_);
lean_dec_ref(v_inst_353_);
v___x_370_ = lean_apply_2(v_toPure_363_, lean_box(0), v_acc_360_);
return v___x_370_;
}
}
else
{
lean_object* v_toBind_371_; lean_object* v_k_372_; lean_object* v_v_373_; lean_object* v_p_374_; lean_object* v___f_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_toBind_371_ = lean_ctor_get(v_inst_353_, 1);
lean_inc_n(v_toBind_371_, 2);
v_k_372_ = lean_ctor_get(v_p_359_, 0);
lean_inc(v_k_372_);
v_v_373_ = lean_ctor_get(v_p_359_, 1);
lean_inc(v_v_373_);
v_p_374_ = lean_ctor_get(v_p_359_, 2);
lean_inc_ref(v_p_374_);
lean_dec_ref(v_p_359_);
lean_inc_ref(v_inst_357_);
lean_inc_ref(v_inst_356_);
lean_inc(v_inst_355_);
lean_inc_ref(v_inst_354_);
lean_inc_ref(v_inst_353_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3), 12, 11);
lean_closure_set(v___f_375_, 0, v_acc_360_);
lean_closure_set(v___f_375_, 1, v_inst_353_);
lean_closure_set(v___f_375_, 2, v_inst_354_);
lean_closure_set(v___f_375_, 3, v_inst_355_);
lean_closure_set(v___f_375_, 4, v_inst_356_);
lean_closure_set(v___f_375_, 5, v_inst_357_);
lean_closure_set(v___f_375_, 6, v_inst_358_);
lean_closure_set(v___f_375_, 7, v_p_374_);
lean_closure_set(v___f_375_, 8, v_k_372_);
lean_closure_set(v___f_375_, 9, v_v_373_);
lean_closure_set(v___f_375_, 10, v_toBind_371_);
v___x_376_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_355_, v_inst_354_, v_inst_353_, v_inst_356_, v_inst_357_);
v___x_377_ = lean_apply_4(v_toBind_371_, lean_box(0), lean_box(0), v___x_376_, v___f_375_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2(lean_object* v_____do__lift_378_, lean_object* v_acc_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_p_386_, lean_object* v_____do__lift_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = l_Lean_mkAppB(v_____do__lift_378_, v_acc_379_, v_____do__lift_387_);
v___x_389_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_380_, v_inst_381_, v_inst_382_, v_inst_383_, v_inst_384_, v_inst_385_, v_p_386_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go(lean_object* v_m_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_p_397_, lean_object* v_acc_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_391_, v_inst_392_, v_inst_393_, v_inst_394_, v_inst_395_, v_inst_396_, v_p_397_, v_acc_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0(lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_p_406_, lean_object* v_____do__lift_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_p_406_, v_____do__lift_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_p_415_){
_start:
{
if (lean_obj_tag(v_p_415_) == 0)
{
lean_object* v_k_416_; lean_object* v___x_417_; 
lean_dec(v_inst_414_);
v_k_416_ = lean_ctor_get(v_p_415_, 0);
lean_inc(v_k_416_);
lean_dec_ref(v_p_415_);
v___x_417_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_inst_413_, v_k_416_);
return v___x_417_;
}
else
{
lean_object* v_toBind_418_; lean_object* v_k_419_; lean_object* v_v_420_; lean_object* v_p_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_toBind_418_ = lean_ctor_get(v_inst_409_, 1);
lean_inc(v_toBind_418_);
v_k_419_ = lean_ctor_get(v_p_415_, 0);
lean_inc(v_k_419_);
v_v_420_ = lean_ctor_get(v_p_415_, 1);
lean_inc(v_v_420_);
v_p_421_ = lean_ctor_get(v_p_415_, 2);
lean_inc_ref(v_p_421_);
lean_dec_ref(v_p_415_);
lean_inc(v_inst_414_);
lean_inc_ref(v_inst_413_);
lean_inc_ref(v_inst_412_);
lean_inc(v_inst_411_);
lean_inc_ref(v_inst_410_);
lean_inc_ref(v_inst_409_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0), 8, 7);
lean_closure_set(v___f_422_, 0, v_inst_409_);
lean_closure_set(v___f_422_, 1, v_inst_410_);
lean_closure_set(v___f_422_, 2, v_inst_411_);
lean_closure_set(v___f_422_, 3, v_inst_412_);
lean_closure_set(v___f_422_, 4, v_inst_413_);
lean_closure_set(v___f_422_, 5, v_inst_414_);
lean_closure_set(v___f_422_, 6, v_p_421_);
v___x_423_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_inst_413_, v_inst_414_, v_k_419_, v_v_420_);
v___x_424_ = lean_apply_4(v_toBind_418_, lean_box(0), lean_box(0), v___x_423_, v___f_422_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly(lean_object* v_m_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_p_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Sym_Arith_denotePoly___redArg(v_inst_426_, v_inst_427_, v_inst_428_, v_inst_429_, v_inst_430_, v_inst_431_, v_p_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0(lean_object* v_k_434_, lean_object* v_toPure_435_, lean_object* v_____do__lift_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = l_Lean_mkNatLit(v_k_434_);
v___x_438_ = l_Lean_Expr_app___override(v_____do__lift_436_, v___x_437_);
v___x_439_ = lean_apply_2(v_toPure_435_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(lean_object* v_k_440_, lean_object* v_toPure_441_, lean_object* v_____do__lift_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = l_Lean_mkIntLit(v_k_440_);
v___x_444_ = l_Lean_Expr_app___override(v_____do__lift_442_, v___x_443_);
v___x_445_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed(lean_object* v_k_446_, lean_object* v_toPure_447_, lean_object* v_____do__lift_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(v_k_446_, v_toPure_447_, v_____do__lift_448_);
lean_dec(v_k_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2(lean_object* v_____do__lift_450_, lean_object* v_toPure_451_, lean_object* v_____do__lift_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l_Lean_Expr_app___override(v_____do__lift_450_, v_____do__lift_452_);
v___x_454_ = lean_apply_2(v_toPure_451_, lean_box(0), v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4(lean_object* v_____do__lift_455_, lean_object* v_____do__lift_456_, lean_object* v_toPure_457_, lean_object* v_____do__lift_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_Lean_mkAppB(v_____do__lift_455_, v_____do__lift_456_, v_____do__lift_458_);
v___x_460_ = lean_apply_2(v_toPure_457_, lean_box(0), v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__13(lean_object* v_k_461_, lean_object* v_____do__lift_462_, lean_object* v_toPure_463_, lean_object* v_____do__lift_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = l_Lean_mkNatLit(v_k_461_);
v___x_466_ = l_Lean_mkAppB(v_____do__lift_462_, v_____do__lift_464_, v___x_465_);
v___x_467_ = lean_apply_2(v_toPure_463_, lean_box(0), v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5(lean_object* v_____do__lift_468_, lean_object* v_toPure_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_getVarExpr_475_, lean_object* v_b_476_, lean_object* v_toBind_477_, lean_object* v_____do__lift_478_){
_start:
{
lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___f_479_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4), 4, 3);
lean_closure_set(v___f_479_, 0, v_____do__lift_468_);
lean_closure_set(v___f_479_, 1, v_____do__lift_478_);
lean_closure_set(v___f_479_, 2, v_toPure_469_);
v___x_480_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_470_, v_inst_471_, v_inst_472_, v_inst_473_, v_inst_474_, v_getVarExpr_475_, v_b_476_);
v___x_481_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v___x_480_, v___f_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6(lean_object* v_toPure_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_getVarExpr_488_, lean_object* v_b_489_, lean_object* v_toBind_490_, lean_object* v_a_491_, lean_object* v_____do__lift_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_toBind_490_);
lean_inc_ref(v_getVarExpr_488_);
lean_inc_ref(v_inst_487_);
lean_inc_ref(v_inst_486_);
lean_inc(v_inst_485_);
lean_inc_ref(v_inst_484_);
lean_inc_ref(v_inst_483_);
v___f_493_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5), 11, 10);
lean_closure_set(v___f_493_, 0, v_____do__lift_492_);
lean_closure_set(v___f_493_, 1, v_toPure_482_);
lean_closure_set(v___f_493_, 2, v_inst_483_);
lean_closure_set(v___f_493_, 3, v_inst_484_);
lean_closure_set(v___f_493_, 4, v_inst_485_);
lean_closure_set(v___f_493_, 5, v_inst_486_);
lean_closure_set(v___f_493_, 6, v_inst_487_);
lean_closure_set(v___f_493_, 7, v_getVarExpr_488_);
lean_closure_set(v___f_493_, 8, v_b_489_);
lean_closure_set(v___f_493_, 9, v_toBind_490_);
v___x_494_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_483_, v_inst_484_, v_inst_485_, v_inst_486_, v_inst_487_, v_getVarExpr_488_, v_a_491_);
v___x_495_ = lean_apply_4(v_toBind_490_, lean_box(0), lean_box(0), v___x_494_, v___f_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__7(lean_object* v_k_496_, lean_object* v_toPure_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_getVarExpr_503_, lean_object* v_a_504_, lean_object* v_toBind_505_, lean_object* v_____do__lift_506_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___f_507_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__13), 4, 3);
lean_closure_set(v___f_507_, 0, v_k_496_);
lean_closure_set(v___f_507_, 1, v_____do__lift_506_);
lean_closure_set(v___f_507_, 2, v_toPure_497_);
v___x_508_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_inst_502_, v_getVarExpr_503_, v_a_504_);
v___x_509_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_508_, v___f_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_getVarExpr_515_, lean_object* v_a_516_){
_start:
{
switch(lean_obj_tag(v_a_516_))
{
case 0:
{
lean_object* v_k_517_; lean_object* v___x_518_; 
lean_dec_ref(v_getVarExpr_515_);
v_k_517_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_k_517_);
lean_dec_ref(v_a_516_);
v___x_518_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_510_, v_inst_511_, v_inst_512_, v_inst_513_, v_inst_514_, v_k_517_);
return v___x_518_;
}
case 1:
{
lean_object* v_toApplicative_519_; lean_object* v_toBind_520_; lean_object* v_toPure_521_; lean_object* v_k_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_toApplicative_519_ = lean_ctor_get(v_inst_510_, 0);
lean_dec_ref(v_getVarExpr_515_);
lean_dec_ref(v_inst_511_);
v_toBind_520_ = lean_ctor_get(v_inst_510_, 1);
lean_inc(v_toBind_520_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_519_, 1);
v_k_522_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_k_522_);
lean_dec_ref(v_a_516_);
lean_inc(v_toPure_521_);
v___f_523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_523_, 0, v_k_522_);
lean_closure_set(v___f_523_, 1, v_toPure_521_);
v___x_524_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_512_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_525_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_524_, v___f_523_);
return v___x_525_;
}
case 2:
{
lean_object* v_toApplicative_526_; lean_object* v_toBind_527_; lean_object* v_toPure_528_; lean_object* v_k_529_; lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_510_, 0);
lean_dec_ref(v_getVarExpr_515_);
lean_dec_ref(v_inst_511_);
v_toBind_527_ = lean_ctor_get(v_inst_510_, 1);
lean_inc(v_toBind_527_);
v_toPure_528_ = lean_ctor_get(v_toApplicative_526_, 1);
v_k_529_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_k_529_);
lean_dec_ref(v_a_516_);
lean_inc(v_toPure_528_);
v___f_530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_530_, 0, v_k_529_);
lean_closure_set(v___f_530_, 1, v_toPure_528_);
v___x_531_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_512_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_532_ = lean_apply_4(v_toBind_527_, lean_box(0), lean_box(0), v___x_531_, v___f_530_);
return v___x_532_;
}
case 3:
{
lean_object* v_toApplicative_533_; lean_object* v_toPure_534_; lean_object* v_i_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_toApplicative_533_ = lean_ctor_get(v_inst_510_, 0);
lean_inc_ref(v_toApplicative_533_);
lean_dec_ref(v_inst_514_);
lean_dec_ref(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_510_);
v_toPure_534_ = lean_ctor_get(v_toApplicative_533_, 1);
lean_inc(v_toPure_534_);
lean_dec_ref(v_toApplicative_533_);
v_i_535_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_i_535_);
lean_dec_ref(v_a_516_);
v___x_536_ = lean_apply_1(v_getVarExpr_515_, v_i_535_);
v___x_537_ = lean_apply_2(v_toPure_534_, lean_box(0), v___x_536_);
return v___x_537_;
}
case 4:
{
lean_object* v_toApplicative_538_; lean_object* v_toBind_539_; lean_object* v_toPure_540_; lean_object* v_a_541_; lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_toApplicative_538_ = lean_ctor_get(v_inst_510_, 0);
v_toBind_539_ = lean_ctor_get(v_inst_510_, 1);
lean_inc_n(v_toBind_539_, 2);
v_toPure_540_ = lean_ctor_get(v_toApplicative_538_, 1);
v_a_541_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_a_541_);
lean_dec_ref(v_a_516_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
lean_inc(v_inst_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_toPure_540_);
v___f_542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3), 10, 9);
lean_closure_set(v___f_542_, 0, v_toPure_540_);
lean_closure_set(v___f_542_, 1, v_inst_510_);
lean_closure_set(v___f_542_, 2, v_inst_511_);
lean_closure_set(v___f_542_, 3, v_inst_512_);
lean_closure_set(v___f_542_, 4, v_inst_513_);
lean_closure_set(v___f_542_, 5, v_inst_514_);
lean_closure_set(v___f_542_, 6, v_getVarExpr_515_);
lean_closure_set(v___f_542_, 7, v_a_541_);
lean_closure_set(v___f_542_, 8, v_toBind_539_);
v___x_543_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_512_, v_inst_511_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_544_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_543_, v___f_542_);
return v___x_544_;
}
case 5:
{
lean_object* v_toApplicative_545_; lean_object* v_toBind_546_; lean_object* v_toPure_547_; lean_object* v_a_548_; lean_object* v_b_549_; lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toApplicative_545_ = lean_ctor_get(v_inst_510_, 0);
v_toBind_546_ = lean_ctor_get(v_inst_510_, 1);
lean_inc_n(v_toBind_546_, 2);
v_toPure_547_ = lean_ctor_get(v_toApplicative_545_, 1);
v_a_548_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_a_548_);
v_b_549_ = lean_ctor_get(v_a_516_, 1);
lean_inc_ref(v_b_549_);
lean_dec_ref(v_a_516_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
lean_inc(v_inst_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_toPure_547_);
v___f_550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_550_, 0, v_toPure_547_);
lean_closure_set(v___f_550_, 1, v_inst_510_);
lean_closure_set(v___f_550_, 2, v_inst_511_);
lean_closure_set(v___f_550_, 3, v_inst_512_);
lean_closure_set(v___f_550_, 4, v_inst_513_);
lean_closure_set(v___f_550_, 5, v_inst_514_);
lean_closure_set(v___f_550_, 6, v_getVarExpr_515_);
lean_closure_set(v___f_550_, 7, v_b_549_);
lean_closure_set(v___f_550_, 8, v_toBind_546_);
lean_closure_set(v___f_550_, 9, v_a_548_);
v___x_551_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_512_, v_inst_511_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_552_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_551_, v___f_550_);
return v___x_552_;
}
case 6:
{
lean_object* v_toApplicative_553_; lean_object* v_toBind_554_; lean_object* v_toPure_555_; lean_object* v_a_556_; lean_object* v_b_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_toApplicative_553_ = lean_ctor_get(v_inst_510_, 0);
v_toBind_554_ = lean_ctor_get(v_inst_510_, 1);
lean_inc_n(v_toBind_554_, 2);
v_toPure_555_ = lean_ctor_get(v_toApplicative_553_, 1);
v_a_556_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_a_556_);
v_b_557_ = lean_ctor_get(v_a_516_, 1);
lean_inc_ref(v_b_557_);
lean_dec_ref(v_a_516_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
lean_inc(v_inst_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_toPure_555_);
v___f_558_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_558_, 0, v_toPure_555_);
lean_closure_set(v___f_558_, 1, v_inst_510_);
lean_closure_set(v___f_558_, 2, v_inst_511_);
lean_closure_set(v___f_558_, 3, v_inst_512_);
lean_closure_set(v___f_558_, 4, v_inst_513_);
lean_closure_set(v___f_558_, 5, v_inst_514_);
lean_closure_set(v___f_558_, 6, v_getVarExpr_515_);
lean_closure_set(v___f_558_, 7, v_b_557_);
lean_closure_set(v___f_558_, 8, v_toBind_554_);
lean_closure_set(v___f_558_, 9, v_a_556_);
v___x_559_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_512_, v_inst_511_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_560_ = lean_apply_4(v_toBind_554_, lean_box(0), lean_box(0), v___x_559_, v___f_558_);
return v___x_560_;
}
case 7:
{
lean_object* v_toApplicative_561_; lean_object* v_toBind_562_; lean_object* v_toPure_563_; lean_object* v_a_564_; lean_object* v_b_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_toApplicative_561_ = lean_ctor_get(v_inst_510_, 0);
v_toBind_562_ = lean_ctor_get(v_inst_510_, 1);
lean_inc_n(v_toBind_562_, 2);
v_toPure_563_ = lean_ctor_get(v_toApplicative_561_, 1);
v_a_564_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_a_564_);
v_b_565_ = lean_ctor_get(v_a_516_, 1);
lean_inc_ref(v_b_565_);
lean_dec_ref(v_a_516_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
lean_inc(v_inst_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_toPure_563_);
v___f_566_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_566_, 0, v_toPure_563_);
lean_closure_set(v___f_566_, 1, v_inst_510_);
lean_closure_set(v___f_566_, 2, v_inst_511_);
lean_closure_set(v___f_566_, 3, v_inst_512_);
lean_closure_set(v___f_566_, 4, v_inst_513_);
lean_closure_set(v___f_566_, 5, v_inst_514_);
lean_closure_set(v___f_566_, 6, v_getVarExpr_515_);
lean_closure_set(v___f_566_, 7, v_b_565_);
lean_closure_set(v___f_566_, 8, v_toBind_562_);
lean_closure_set(v___f_566_, 9, v_a_564_);
v___x_567_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_512_, v_inst_511_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_568_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v___x_567_, v___f_566_);
return v___x_568_;
}
default: 
{
lean_object* v_toApplicative_569_; lean_object* v_toBind_570_; lean_object* v_toPure_571_; lean_object* v_a_572_; lean_object* v_k_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_toApplicative_569_ = lean_ctor_get(v_inst_510_, 0);
v_toBind_570_ = lean_ctor_get(v_inst_510_, 1);
lean_inc_n(v_toBind_570_, 2);
v_toPure_571_ = lean_ctor_get(v_toApplicative_569_, 1);
v_a_572_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_a_572_);
v_k_573_ = lean_ctor_get(v_a_516_, 1);
lean_inc(v_k_573_);
lean_dec_ref(v_a_516_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
lean_inc(v_inst_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_toPure_571_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__7), 11, 10);
lean_closure_set(v___f_574_, 0, v_k_573_);
lean_closure_set(v___f_574_, 1, v_toPure_571_);
lean_closure_set(v___f_574_, 2, v_inst_510_);
lean_closure_set(v___f_574_, 3, v_inst_511_);
lean_closure_set(v___f_574_, 4, v_inst_512_);
lean_closure_set(v___f_574_, 5, v_inst_513_);
lean_closure_set(v___f_574_, 6, v_inst_514_);
lean_closure_set(v___f_574_, 7, v_getVarExpr_515_);
lean_closure_set(v___f_574_, 8, v_a_572_);
lean_closure_set(v___f_574_, 9, v_toBind_570_);
v___x_575_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_512_, v_inst_511_, v_inst_510_, v_inst_513_, v_inst_514_);
v___x_576_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v___x_575_, v___f_574_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3(lean_object* v_toPure_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_getVarExpr_583_, lean_object* v_a_584_, lean_object* v_toBind_585_, lean_object* v_____do__lift_586_){
_start:
{
lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2), 3, 2);
lean_closure_set(v___f_587_, 0, v_____do__lift_586_);
lean_closure_set(v___f_587_, 1, v_toPure_577_);
v___x_588_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_getVarExpr_583_, v_a_584_);
v___x_589_ = lean_apply_4(v_toBind_585_, lean_box(0), lean_box(0), v___x_588_, v___f_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go(lean_object* v_m_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_getVarExpr_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_591_, v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_getVarExpr_596_, v_a_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore___redArg(lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_getVarExpr_604_, lean_object* v_e_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_getVarExpr_604_, v_e_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore(lean_object* v_m_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_getVarExpr_613_, lean_object* v_e_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_608_, v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_getVarExpr_613_, v_e_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(lean_object* v___x_616_, lean_object* v_vars_617_, lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_get_borrowed(v___x_616_, v_vars_617_, v_x_618_);
lean_inc(v___x_619_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed(lean_object* v___x_620_, lean_object* v_vars_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(v___x_620_, v_vars_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec_ref(v_vars_621_);
lean_dec_ref(v___x_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_vars_629_, lean_object* v_e_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___f_632_; lean_object* v___x_633_; 
v___x_631_ = l_Lean_instInhabitedExpr;
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_632_, 0, v___x_631_);
lean_closure_set(v___f_632_, 1, v_vars_629_);
v___x_633_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v___f_632_, v_e_630_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr(lean_object* v_m_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_vars_640_, lean_object* v_e_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(v_inst_635_, v_inst_636_, v_inst_637_, v_inst_638_, v_inst_639_, v_vars_640_, v_e_641_);
return v___x_642_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_DenoteExpr(builtin);
}
#ifdef __cplusplus
}
#endif
