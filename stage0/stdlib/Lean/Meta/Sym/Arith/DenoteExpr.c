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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_____do__lift_65_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0(lean_object* v_k_123_, lean_object* v_x_124_, lean_object* v_toPure_125_, lean_object* v_____do__lift_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = l_Lean_mkNatLit(v_k_123_);
v___x_128_ = l_Lean_mkAppB(v_____do__lift_126_, v_x_124_, v___x_127_);
v___x_129_ = lean_apply_2(v_toPure_125_, lean_box(0), v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1(lean_object* v_k_130_, lean_object* v_toPure_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_toBind_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_dec_eq(v_k_130_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__0), 4, 3);
lean_closure_set(v___f_141_, 0, v_k_130_);
lean_closure_set(v___f_141_, 1, v_x_138_);
lean_closure_set(v___f_141_, 2, v_toPure_131_);
v___x_142_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_132_, v_inst_133_, v_inst_134_, v_inst_135_, v_inst_136_);
v___x_143_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_142_, v___f_141_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_toBind_137_);
lean_dec_ref(v_inst_136_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
lean_dec_ref(v_inst_133_);
lean_dec(v_inst_132_);
lean_dec(v_k_130_);
v___x_144_ = lean_apply_2(v_toPure_131_, lean_box(0), v_x_138_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_pw_151_){
_start:
{
lean_object* v_toApplicative_152_; lean_object* v_toBind_153_; lean_object* v_x_154_; lean_object* v_k_155_; lean_object* v_toPure_156_; lean_object* v___x_157_; lean_object* v___f_158_; lean_object* v___x_159_; 
v_toApplicative_152_ = lean_ctor_get(v_inst_145_, 0);
v_toBind_153_ = lean_ctor_get(v_inst_145_, 1);
lean_inc_n(v_toBind_153_, 2);
v_x_154_ = lean_ctor_get(v_pw_151_, 0);
lean_inc(v_x_154_);
v_k_155_ = lean_ctor_get(v_pw_151_, 1);
lean_inc(v_k_155_);
lean_dec_ref(v_pw_151_);
v_toPure_156_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_inc(v_toPure_156_);
v___x_157_ = lean_apply_1(v_inst_150_, v_x_154_);
v___f_158_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePower___redArg___lam__1), 9, 8);
lean_closure_set(v___f_158_, 0, v_k_155_);
lean_closure_set(v___f_158_, 1, v_toPure_156_);
lean_closure_set(v___f_158_, 2, v_inst_147_);
lean_closure_set(v___f_158_, 3, v_inst_146_);
lean_closure_set(v___f_158_, 4, v_inst_145_);
lean_closure_set(v___f_158_, 5, v_inst_148_);
lean_closure_set(v___f_158_, 6, v_inst_149_);
lean_closure_set(v___f_158_, 7, v_toBind_153_);
v___x_159_ = lean_apply_4(v_toBind_153_, lean_box(0), lean_box(0), v___x_157_, v___f_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower(lean_object* v_m_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_pw_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_161_, v_inst_162_, v_inst_163_, v_inst_164_, v_inst_165_, v_inst_166_, v_pw_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1(lean_object* v_acc_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_m_176_, lean_object* v_p_177_, lean_object* v_toBind_178_, lean_object* v_____do__lift_179_){
_start:
{
lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc(v_inst_175_);
lean_inc_ref(v_inst_174_);
lean_inc_ref(v_inst_173_);
lean_inc(v_inst_172_);
lean_inc_ref(v_inst_171_);
lean_inc_ref(v_inst_170_);
v___f_180_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0), 10, 9);
lean_closure_set(v___f_180_, 0, v_____do__lift_179_);
lean_closure_set(v___f_180_, 1, v_acc_169_);
lean_closure_set(v___f_180_, 2, v_inst_170_);
lean_closure_set(v___f_180_, 3, v_inst_171_);
lean_closure_set(v___f_180_, 4, v_inst_172_);
lean_closure_set(v___f_180_, 5, v_inst_173_);
lean_closure_set(v___f_180_, 6, v_inst_174_);
lean_closure_set(v___f_180_, 7, v_inst_175_);
lean_closure_set(v___f_180_, 8, v_m_176_);
v___x_181_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_170_, v_inst_171_, v_inst_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_p_177_);
v___x_182_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v___x_181_, v___f_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_mn_189_, lean_object* v_acc_190_){
_start:
{
if (lean_obj_tag(v_mn_189_) == 0)
{
lean_object* v_toApplicative_191_; lean_object* v_toPure_192_; lean_object* v___x_193_; 
v_toApplicative_191_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_toApplicative_191_);
lean_dec(v_inst_188_);
lean_dec_ref(v_inst_187_);
lean_dec_ref(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec_ref(v_inst_184_);
lean_dec_ref(v_inst_183_);
v_toPure_192_ = lean_ctor_get(v_toApplicative_191_, 1);
lean_inc(v_toPure_192_);
lean_dec_ref(v_toApplicative_191_);
v___x_193_ = lean_apply_2(v_toPure_192_, lean_box(0), v_acc_190_);
return v___x_193_;
}
else
{
lean_object* v_toBind_194_; lean_object* v_p_195_; lean_object* v_m_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_toBind_194_ = lean_ctor_get(v_inst_183_, 1);
lean_inc_n(v_toBind_194_, 2);
v_p_195_ = lean_ctor_get(v_mn_189_, 0);
lean_inc_ref(v_p_195_);
v_m_196_ = lean_ctor_get(v_mn_189_, 1);
lean_inc(v_m_196_);
lean_dec_ref_known(v_mn_189_, 2);
lean_inc_ref(v_inst_187_);
lean_inc_ref(v_inst_186_);
lean_inc(v_inst_185_);
lean_inc_ref(v_inst_184_);
lean_inc_ref(v_inst_183_);
v___f_197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_197_, 0, v_acc_190_);
lean_closure_set(v___f_197_, 1, v_inst_183_);
lean_closure_set(v___f_197_, 2, v_inst_184_);
lean_closure_set(v___f_197_, 3, v_inst_185_);
lean_closure_set(v___f_197_, 4, v_inst_186_);
lean_closure_set(v___f_197_, 5, v_inst_187_);
lean_closure_set(v___f_197_, 6, v_inst_188_);
lean_closure_set(v___f_197_, 7, v_m_196_);
lean_closure_set(v___f_197_, 8, v_p_195_);
lean_closure_set(v___f_197_, 9, v_toBind_194_);
v___x_198_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_185_, v_inst_184_, v_inst_183_, v_inst_186_, v_inst_187_);
v___x_199_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_198_, v___f_197_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg___lam__0(lean_object* v_____do__lift_200_, lean_object* v_acc_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_____do__lift_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Lean_mkAppB(v_____do__lift_200_, v_acc_201_, v_____do__lift_209_);
v___x_211_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_202_, v_inst_203_, v_inst_204_, v_inst_205_, v_inst_206_, v_inst_207_, v_m_208_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go(lean_object* v_m_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_mn_219_, lean_object* v_acc_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_213_, v_inst_214_, v_inst_215_, v_inst_216_, v_inst_217_, v_inst_218_, v_mn_219_, v_acc_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_m_228_, lean_object* v_____do__lift_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___redArg(v_inst_222_, v_inst_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_inst_227_, v_m_228_, v_____do__lift_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_to_int(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___redArg(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_mn_239_){
_start:
{
if (lean_obj_tag(v_mn_239_) == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_inst_238_);
v___x_240_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0);
v___x_241_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_233_, v_inst_234_, v_inst_235_, v_inst_236_, v_inst_237_, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_toBind_242_; lean_object* v_p_243_; lean_object* v_m_244_; lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_toBind_242_ = lean_ctor_get(v_inst_233_, 1);
lean_inc(v_toBind_242_);
v_p_243_ = lean_ctor_get(v_mn_239_, 0);
lean_inc_ref(v_p_243_);
v_m_244_ = lean_ctor_get(v_mn_239_, 1);
lean_inc(v_m_244_);
lean_dec_ref_known(v_mn_239_, 2);
lean_inc(v_inst_238_);
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
lean_inc(v_inst_235_);
lean_inc_ref(v_inst_234_);
lean_inc_ref(v_inst_233_);
v___f_245_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteMon___redArg___lam__0), 8, 7);
lean_closure_set(v___f_245_, 0, v_inst_233_);
lean_closure_set(v___f_245_, 1, v_inst_234_);
lean_closure_set(v___f_245_, 2, v_inst_235_);
lean_closure_set(v___f_245_, 3, v_inst_236_);
lean_closure_set(v___f_245_, 4, v_inst_237_);
lean_closure_set(v___f_245_, 5, v_inst_238_);
lean_closure_set(v___f_245_, 6, v_m_244_);
v___x_246_ = l_Lean_Meta_Sym_Arith_denotePower___redArg(v_inst_233_, v_inst_234_, v_inst_235_, v_inst_236_, v_inst_237_, v_inst_238_, v_p_243_);
v___x_247_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_246_, v___f_245_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon(lean_object* v_m_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_mn_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_249_, v_inst_250_, v_inst_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_mn_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0(lean_object* v_____do__lift_257_, lean_object* v_____do__lift_258_, lean_object* v_toPure_259_, lean_object* v_____do__lift_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = l_Lean_mkAppB(v_____do__lift_257_, v_____do__lift_258_, v_____do__lift_260_);
v___x_262_ = lean_apply_2(v_toPure_259_, lean_box(0), v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1(lean_object* v_____do__lift_263_, lean_object* v_toPure_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_mn_271_, lean_object* v_toBind_272_, lean_object* v_____do__lift_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___f_274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0), 4, 3);
lean_closure_set(v___f_274_, 0, v_____do__lift_263_);
lean_closure_set(v___f_274_, 1, v_____do__lift_273_);
lean_closure_set(v___f_274_, 2, v_toPure_264_);
v___x_275_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_265_, v_inst_266_, v_inst_267_, v_inst_268_, v_inst_269_, v_inst_270_, v_mn_271_);
v___x_276_ = lean_apply_4(v_toBind_272_, lean_box(0), lean_box(0), v___x_275_, v___f_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2(lean_object* v_toPure_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_mn_284_, lean_object* v_toBind_285_, lean_object* v_k_286_, lean_object* v_____do__lift_287_){
_start:
{
lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc(v_toBind_285_);
lean_inc_ref(v_inst_282_);
lean_inc_ref(v_inst_281_);
lean_inc(v_inst_280_);
lean_inc_ref(v_inst_279_);
lean_inc_ref(v_inst_278_);
v___f_288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__1), 11, 10);
lean_closure_set(v___f_288_, 0, v_____do__lift_287_);
lean_closure_set(v___f_288_, 1, v_toPure_277_);
lean_closure_set(v___f_288_, 2, v_inst_278_);
lean_closure_set(v___f_288_, 3, v_inst_279_);
lean_closure_set(v___f_288_, 4, v_inst_280_);
lean_closure_set(v___f_288_, 5, v_inst_281_);
lean_closure_set(v___f_288_, 6, v_inst_282_);
lean_closure_set(v___f_288_, 7, v_inst_283_);
lean_closure_set(v___f_288_, 8, v_mn_284_);
lean_closure_set(v___f_288_, 9, v_toBind_285_);
v___x_289_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_278_, v_inst_279_, v_inst_280_, v_inst_281_, v_inst_282_, v_k_286_);
v___x_290_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v___x_289_, v___f_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_k_297_, lean_object* v_mn_298_){
_start:
{
lean_object* v_toApplicative_299_; lean_object* v_toBind_300_; lean_object* v_toPure_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_toApplicative_299_ = lean_ctor_get(v_inst_291_, 0);
v_toBind_300_ = lean_ctor_get(v_inst_291_, 1);
v_toPure_301_ = lean_ctor_get(v_toApplicative_299_, 1);
v___x_302_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___redArg___closed__0);
v___x_303_ = lean_int_dec_eq(v_k_297_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc_n(v_toBind_300_, 2);
lean_inc_ref(v_inst_295_);
lean_inc_ref(v_inst_294_);
lean_inc(v_inst_293_);
lean_inc_ref(v_inst_292_);
lean_inc_ref(v_inst_291_);
lean_inc(v_toPure_301_);
v___f_304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__2), 11, 10);
lean_closure_set(v___f_304_, 0, v_toPure_301_);
lean_closure_set(v___f_304_, 1, v_inst_291_);
lean_closure_set(v___f_304_, 2, v_inst_292_);
lean_closure_set(v___f_304_, 3, v_inst_293_);
lean_closure_set(v___f_304_, 4, v_inst_294_);
lean_closure_set(v___f_304_, 5, v_inst_295_);
lean_closure_set(v___f_304_, 6, v_inst_296_);
lean_closure_set(v___f_304_, 7, v_mn_298_);
lean_closure_set(v___f_304_, 8, v_toBind_300_);
lean_closure_set(v___f_304_, 9, v_k_297_);
v___x_305_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_293_, v_inst_292_, v_inst_291_, v_inst_294_, v_inst_295_);
v___x_306_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_305_, v___f_304_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
lean_dec(v_k_297_);
v___x_307_ = l_Lean_Meta_Sym_Arith_denoteMon___redArg(v_inst_291_, v_inst_292_, v_inst_293_, v_inst_294_, v_inst_295_, v_inst_296_, v_mn_298_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm(lean_object* v_m_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_k_315_, lean_object* v_mn_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_309_, v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_k_315_, v_mn_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0(lean_object* v_____do__lift_318_, lean_object* v_acc_319_, lean_object* v_toPure_320_, lean_object* v_____do__lift_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Lean_mkAppB(v_____do__lift_318_, v_acc_319_, v_____do__lift_321_);
v___x_323_ = lean_apply_2(v_toPure_320_, lean_box(0), v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1(lean_object* v_acc_324_, lean_object* v_toPure_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_k_331_, lean_object* v_toBind_332_, lean_object* v_____do__lift_333_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___f_334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__0), 4, 3);
lean_closure_set(v___f_334_, 0, v_____do__lift_333_);
lean_closure_set(v___f_334_, 1, v_acc_324_);
lean_closure_set(v___f_334_, 2, v_toPure_325_);
v___x_335_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_326_, v_inst_327_, v_inst_328_, v_inst_329_, v_inst_330_, v_k_331_);
v___x_336_ = lean_apply_4(v_toBind_332_, lean_box(0), lean_box(0), v___x_335_, v___f_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3(lean_object* v_acc_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_p_344_, lean_object* v_k_345_, lean_object* v_v_346_, lean_object* v_toBind_347_, lean_object* v_____do__lift_348_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_inc(v_inst_343_);
lean_inc_ref(v_inst_342_);
lean_inc_ref(v_inst_341_);
lean_inc(v_inst_340_);
lean_inc_ref(v_inst_339_);
lean_inc_ref(v_inst_338_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2), 10, 9);
lean_closure_set(v___f_349_, 0, v_____do__lift_348_);
lean_closure_set(v___f_349_, 1, v_acc_337_);
lean_closure_set(v___f_349_, 2, v_inst_338_);
lean_closure_set(v___f_349_, 3, v_inst_339_);
lean_closure_set(v___f_349_, 4, v_inst_340_);
lean_closure_set(v___f_349_, 5, v_inst_341_);
lean_closure_set(v___f_349_, 6, v_inst_342_);
lean_closure_set(v___f_349_, 7, v_inst_343_);
lean_closure_set(v___f_349_, 8, v_p_344_);
v___x_350_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_338_, v_inst_339_, v_inst_340_, v_inst_341_, v_inst_342_, v_inst_343_, v_k_345_, v_v_346_);
v___x_351_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_350_, v___f_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_p_358_, lean_object* v_acc_359_){
_start:
{
if (lean_obj_tag(v_p_358_) == 0)
{
lean_object* v_toApplicative_360_; lean_object* v_toBind_361_; lean_object* v_toPure_362_; lean_object* v_k_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_toApplicative_360_ = lean_ctor_get(v_inst_352_, 0);
lean_dec(v_inst_357_);
v_toBind_361_ = lean_ctor_get(v_inst_352_, 1);
lean_inc(v_toBind_361_);
v_toPure_362_ = lean_ctor_get(v_toApplicative_360_, 1);
v_k_363_ = lean_ctor_get(v_p_358_, 0);
lean_inc(v_k_363_);
lean_dec_ref_known(v_p_358_, 1);
v___x_364_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___redArg___lam__1___closed__1);
v___x_365_ = lean_int_dec_eq(v_k_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc(v_toBind_361_);
lean_inc_ref(v_inst_356_);
lean_inc_ref(v_inst_355_);
lean_inc(v_inst_354_);
lean_inc_ref(v_inst_353_);
lean_inc_ref(v_inst_352_);
lean_inc(v_toPure_362_);
v___f_366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__1), 10, 9);
lean_closure_set(v___f_366_, 0, v_acc_359_);
lean_closure_set(v___f_366_, 1, v_toPure_362_);
lean_closure_set(v___f_366_, 2, v_inst_352_);
lean_closure_set(v___f_366_, 3, v_inst_353_);
lean_closure_set(v___f_366_, 4, v_inst_354_);
lean_closure_set(v___f_366_, 5, v_inst_355_);
lean_closure_set(v___f_366_, 6, v_inst_356_);
lean_closure_set(v___f_366_, 7, v_k_363_);
lean_closure_set(v___f_366_, 8, v_toBind_361_);
v___x_367_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_354_, v_inst_353_, v_inst_352_, v_inst_355_, v_inst_356_);
v___x_368_ = lean_apply_4(v_toBind_361_, lean_box(0), lean_box(0), v___x_367_, v___f_366_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
lean_inc(v_toPure_362_);
lean_dec(v_k_363_);
lean_dec(v_toBind_361_);
lean_dec_ref(v_inst_356_);
lean_dec_ref(v_inst_355_);
lean_dec(v_inst_354_);
lean_dec_ref(v_inst_353_);
lean_dec_ref(v_inst_352_);
v___x_369_ = lean_apply_2(v_toPure_362_, lean_box(0), v_acc_359_);
return v___x_369_;
}
}
else
{
lean_object* v_toBind_370_; lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v_p_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_toBind_370_ = lean_ctor_get(v_inst_352_, 1);
lean_inc_n(v_toBind_370_, 2);
v_k_371_ = lean_ctor_get(v_p_358_, 0);
lean_inc(v_k_371_);
v_v_372_ = lean_ctor_get(v_p_358_, 1);
lean_inc(v_v_372_);
v_p_373_ = lean_ctor_get(v_p_358_, 2);
lean_inc_ref(v_p_373_);
lean_dec_ref_known(v_p_358_, 3);
lean_inc_ref(v_inst_356_);
lean_inc_ref(v_inst_355_);
lean_inc(v_inst_354_);
lean_inc_ref(v_inst_353_);
lean_inc_ref(v_inst_352_);
v___f_374_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__3), 12, 11);
lean_closure_set(v___f_374_, 0, v_acc_359_);
lean_closure_set(v___f_374_, 1, v_inst_352_);
lean_closure_set(v___f_374_, 2, v_inst_353_);
lean_closure_set(v___f_374_, 3, v_inst_354_);
lean_closure_set(v___f_374_, 4, v_inst_355_);
lean_closure_set(v___f_374_, 5, v_inst_356_);
lean_closure_set(v___f_374_, 6, v_inst_357_);
lean_closure_set(v___f_374_, 7, v_p_373_);
lean_closure_set(v___f_374_, 8, v_k_371_);
lean_closure_set(v___f_374_, 9, v_v_372_);
lean_closure_set(v___f_374_, 10, v_toBind_370_);
v___x_375_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_354_, v_inst_353_, v_inst_352_, v_inst_355_, v_inst_356_);
v___x_376_ = lean_apply_4(v_toBind_370_, lean_box(0), lean_box(0), v___x_375_, v___f_374_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg___lam__2(lean_object* v_____do__lift_377_, lean_object* v_acc_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_p_385_, lean_object* v_____do__lift_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = l_Lean_mkAppB(v_____do__lift_377_, v_acc_378_, v_____do__lift_386_);
v___x_388_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_379_, v_inst_380_, v_inst_381_, v_inst_382_, v_inst_383_, v_inst_384_, v_p_385_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go(lean_object* v_m_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_p_396_, lean_object* v_acc_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_390_, v_inst_391_, v_inst_392_, v_inst_393_, v_inst_394_, v_inst_395_, v_p_396_, v_acc_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0(lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_p_405_, lean_object* v_____do__lift_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___redArg(v_inst_399_, v_inst_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_p_405_, v_____do__lift_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___redArg(lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_p_414_){
_start:
{
if (lean_obj_tag(v_p_414_) == 0)
{
lean_object* v_k_415_; lean_object* v___x_416_; 
lean_dec(v_inst_413_);
v_k_415_ = lean_ctor_get(v_p_414_, 0);
lean_inc(v_k_415_);
lean_dec_ref_known(v_p_414_, 1);
v___x_416_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_k_415_);
return v___x_416_;
}
else
{
lean_object* v_toBind_417_; lean_object* v_k_418_; lean_object* v_v_419_; lean_object* v_p_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_toBind_417_ = lean_ctor_get(v_inst_408_, 1);
lean_inc(v_toBind_417_);
v_k_418_ = lean_ctor_get(v_p_414_, 0);
lean_inc(v_k_418_);
v_v_419_ = lean_ctor_get(v_p_414_, 1);
lean_inc(v_v_419_);
v_p_420_ = lean_ctor_get(v_p_414_, 2);
lean_inc_ref(v_p_420_);
lean_dec_ref_known(v_p_414_, 3);
lean_inc(v_inst_413_);
lean_inc_ref(v_inst_412_);
lean_inc_ref(v_inst_411_);
lean_inc(v_inst_410_);
lean_inc_ref(v_inst_409_);
lean_inc_ref(v_inst_408_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denotePoly___redArg___lam__0), 8, 7);
lean_closure_set(v___f_421_, 0, v_inst_408_);
lean_closure_set(v___f_421_, 1, v_inst_409_);
lean_closure_set(v___f_421_, 2, v_inst_410_);
lean_closure_set(v___f_421_, 3, v_inst_411_);
lean_closure_set(v___f_421_, 4, v_inst_412_);
lean_closure_set(v___f_421_, 5, v_inst_413_);
lean_closure_set(v___f_421_, 6, v_p_420_);
v___x_422_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_inst_413_, v_k_418_, v_v_419_);
v___x_423_ = lean_apply_4(v_toBind_417_, lean_box(0), lean_box(0), v___x_422_, v___f_421_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly(lean_object* v_m_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_p_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_Sym_Arith_denotePoly___redArg(v_inst_425_, v_inst_426_, v_inst_427_, v_inst_428_, v_inst_429_, v_inst_430_, v_p_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0(lean_object* v_k_433_, lean_object* v_toPure_434_, lean_object* v_____do__lift_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_mkNatLit(v_k_433_);
v___x_437_ = l_Lean_Expr_app___override(v_____do__lift_435_, v___x_436_);
v___x_438_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(lean_object* v_k_439_, lean_object* v_toPure_440_, lean_object* v_____do__lift_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_mkIntLit(v_k_439_);
v___x_443_ = l_Lean_Expr_app___override(v_____do__lift_441_, v___x_442_);
v___x_444_ = lean_apply_2(v_toPure_440_, lean_box(0), v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed(lean_object* v_k_445_, lean_object* v_toPure_446_, lean_object* v_____do__lift_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1(v_k_445_, v_toPure_446_, v_____do__lift_447_);
lean_dec(v_k_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2(lean_object* v_____do__lift_449_, lean_object* v_toPure_450_, lean_object* v_____do__lift_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l_Lean_Expr_app___override(v_____do__lift_449_, v_____do__lift_451_);
v___x_453_ = lean_apply_2(v_toPure_450_, lean_box(0), v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__12(lean_object* v_k_454_, lean_object* v_____do__lift_455_, lean_object* v_toPure_456_, lean_object* v_____do__lift_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_mkNatLit(v_k_454_);
v___x_459_ = l_Lean_mkAppB(v_____do__lift_455_, v_____do__lift_457_, v___x_458_);
v___x_460_ = lean_apply_2(v_toPure_456_, lean_box(0), v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5(lean_object* v_____do__lift_461_, lean_object* v_toPure_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_getVarExpr_468_, lean_object* v_b_469_, lean_object* v_toBind_470_, lean_object* v_____do__lift_471_){
_start:
{
lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___f_472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___redArg___lam__0), 4, 3);
lean_closure_set(v___f_472_, 0, v_____do__lift_461_);
lean_closure_set(v___f_472_, 1, v_____do__lift_471_);
lean_closure_set(v___f_472_, 2, v_toPure_462_);
v___x_473_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_inst_467_, v_getVarExpr_468_, v_b_469_);
v___x_474_ = lean_apply_4(v_toBind_470_, lean_box(0), lean_box(0), v___x_473_, v___f_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4(lean_object* v_toPure_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_getVarExpr_481_, lean_object* v_b_482_, lean_object* v_toBind_483_, lean_object* v_a_484_, lean_object* v_____do__lift_485_){
_start:
{
lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_toBind_483_);
lean_inc_ref(v_getVarExpr_481_);
lean_inc_ref(v_inst_480_);
lean_inc_ref(v_inst_479_);
lean_inc(v_inst_478_);
lean_inc_ref(v_inst_477_);
lean_inc_ref(v_inst_476_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__5), 11, 10);
lean_closure_set(v___f_486_, 0, v_____do__lift_485_);
lean_closure_set(v___f_486_, 1, v_toPure_475_);
lean_closure_set(v___f_486_, 2, v_inst_476_);
lean_closure_set(v___f_486_, 3, v_inst_477_);
lean_closure_set(v___f_486_, 4, v_inst_478_);
lean_closure_set(v___f_486_, 5, v_inst_479_);
lean_closure_set(v___f_486_, 6, v_inst_480_);
lean_closure_set(v___f_486_, 7, v_getVarExpr_481_);
lean_closure_set(v___f_486_, 8, v_b_482_);
lean_closure_set(v___f_486_, 9, v_toBind_483_);
v___x_487_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_476_, v_inst_477_, v_inst_478_, v_inst_479_, v_inst_480_, v_getVarExpr_481_, v_a_484_);
v___x_488_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_487_, v___f_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6(lean_object* v_k_489_, lean_object* v_toPure_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_getVarExpr_496_, lean_object* v_a_497_, lean_object* v_toBind_498_, lean_object* v_____do__lift_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___f_500_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__12), 4, 3);
lean_closure_set(v___f_500_, 0, v_k_489_);
lean_closure_set(v___f_500_, 1, v_____do__lift_499_);
lean_closure_set(v___f_500_, 2, v_toPure_490_);
v___x_501_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_491_, v_inst_492_, v_inst_493_, v_inst_494_, v_inst_495_, v_getVarExpr_496_, v_a_497_);
v___x_502_ = lean_apply_4(v_toBind_498_, lean_box(0), lean_box(0), v___x_501_, v___f_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_getVarExpr_508_, lean_object* v_a_509_){
_start:
{
switch(lean_obj_tag(v_a_509_))
{
case 0:
{
lean_object* v_k_510_; lean_object* v___x_511_; 
lean_dec_ref(v_getVarExpr_508_);
v_k_510_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_k_510_);
lean_dec_ref_known(v_a_509_, 1);
v___x_511_ = l_Lean_Meta_Sym_Arith_denoteNum___redArg(v_inst_503_, v_inst_504_, v_inst_505_, v_inst_506_, v_inst_507_, v_k_510_);
return v___x_511_;
}
case 1:
{
lean_object* v_toApplicative_512_; lean_object* v_toBind_513_; lean_object* v_toPure_514_; lean_object* v_k_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_toApplicative_512_ = lean_ctor_get(v_inst_503_, 0);
lean_dec_ref(v_getVarExpr_508_);
lean_dec_ref(v_inst_504_);
v_toBind_513_ = lean_ctor_get(v_inst_503_, 1);
lean_inc(v_toBind_513_);
v_toPure_514_ = lean_ctor_get(v_toApplicative_512_, 1);
v_k_515_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_k_515_);
lean_dec_ref_known(v_a_509_, 1);
lean_inc(v_toPure_514_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_516_, 0, v_k_515_);
lean_closure_set(v___f_516_, 1, v_toPure_514_);
v___x_517_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_505_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_518_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v___x_517_, v___f_516_);
return v___x_518_;
}
case 2:
{
lean_object* v_toApplicative_519_; lean_object* v_toBind_520_; lean_object* v_toPure_521_; lean_object* v_k_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_toApplicative_519_ = lean_ctor_get(v_inst_503_, 0);
lean_dec_ref(v_getVarExpr_508_);
lean_dec_ref(v_inst_504_);
v_toBind_520_ = lean_ctor_get(v_inst_503_, 1);
lean_inc(v_toBind_520_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_519_, 1);
v_k_522_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_k_522_);
lean_dec_ref_known(v_a_509_, 1);
lean_inc(v_toPure_521_);
v___f_523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_523_, 0, v_k_522_);
lean_closure_set(v___f_523_, 1, v_toPure_521_);
v___x_524_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_505_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_525_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_524_, v___f_523_);
return v___x_525_;
}
case 3:
{
lean_object* v_toApplicative_526_; lean_object* v_toPure_527_; lean_object* v_i_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_503_, 0);
lean_inc_ref(v_toApplicative_526_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec(v_inst_505_);
lean_dec_ref(v_inst_504_);
lean_dec_ref(v_inst_503_);
v_toPure_527_ = lean_ctor_get(v_toApplicative_526_, 1);
lean_inc(v_toPure_527_);
lean_dec_ref(v_toApplicative_526_);
v_i_528_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_i_528_);
lean_dec_ref_known(v_a_509_, 1);
v___x_529_ = lean_apply_1(v_getVarExpr_508_, v_i_528_);
v___x_530_ = lean_apply_2(v_toPure_527_, lean_box(0), v___x_529_);
return v___x_530_;
}
case 4:
{
lean_object* v_toApplicative_531_; lean_object* v_toBind_532_; lean_object* v_toPure_533_; lean_object* v_a_534_; lean_object* v___f_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_toApplicative_531_ = lean_ctor_get(v_inst_503_, 0);
v_toBind_532_ = lean_ctor_get(v_inst_503_, 1);
lean_inc_n(v_toBind_532_, 2);
v_toPure_533_ = lean_ctor_get(v_toApplicative_531_, 1);
v_a_534_ = lean_ctor_get(v_a_509_, 0);
lean_inc_ref(v_a_534_);
lean_dec_ref_known(v_a_509_, 1);
lean_inc_ref(v_inst_507_);
lean_inc_ref(v_inst_506_);
lean_inc(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_503_);
lean_inc(v_toPure_533_);
v___f_535_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3), 10, 9);
lean_closure_set(v___f_535_, 0, v_toPure_533_);
lean_closure_set(v___f_535_, 1, v_inst_503_);
lean_closure_set(v___f_535_, 2, v_inst_504_);
lean_closure_set(v___f_535_, 3, v_inst_505_);
lean_closure_set(v___f_535_, 4, v_inst_506_);
lean_closure_set(v___f_535_, 5, v_inst_507_);
lean_closure_set(v___f_535_, 6, v_getVarExpr_508_);
lean_closure_set(v___f_535_, 7, v_a_534_);
lean_closure_set(v___f_535_, 8, v_toBind_532_);
v___x_536_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_505_, v_inst_504_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_537_ = lean_apply_4(v_toBind_532_, lean_box(0), lean_box(0), v___x_536_, v___f_535_);
return v___x_537_;
}
case 5:
{
lean_object* v_toApplicative_538_; lean_object* v_toBind_539_; lean_object* v_toPure_540_; lean_object* v_a_541_; lean_object* v_b_542_; lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_toApplicative_538_ = lean_ctor_get(v_inst_503_, 0);
v_toBind_539_ = lean_ctor_get(v_inst_503_, 1);
lean_inc_n(v_toBind_539_, 2);
v_toPure_540_ = lean_ctor_get(v_toApplicative_538_, 1);
v_a_541_ = lean_ctor_get(v_a_509_, 0);
lean_inc_ref(v_a_541_);
v_b_542_ = lean_ctor_get(v_a_509_, 1);
lean_inc_ref(v_b_542_);
lean_dec_ref_known(v_a_509_, 2);
lean_inc_ref(v_inst_507_);
lean_inc_ref(v_inst_506_);
lean_inc(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_503_);
lean_inc(v_toPure_540_);
v___f_543_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4), 11, 10);
lean_closure_set(v___f_543_, 0, v_toPure_540_);
lean_closure_set(v___f_543_, 1, v_inst_503_);
lean_closure_set(v___f_543_, 2, v_inst_504_);
lean_closure_set(v___f_543_, 3, v_inst_505_);
lean_closure_set(v___f_543_, 4, v_inst_506_);
lean_closure_set(v___f_543_, 5, v_inst_507_);
lean_closure_set(v___f_543_, 6, v_getVarExpr_508_);
lean_closure_set(v___f_543_, 7, v_b_542_);
lean_closure_set(v___f_543_, 8, v_toBind_539_);
lean_closure_set(v___f_543_, 9, v_a_541_);
v___x_544_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_505_, v_inst_504_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_545_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_544_, v___f_543_);
return v___x_545_;
}
case 6:
{
lean_object* v_toApplicative_546_; lean_object* v_toBind_547_; lean_object* v_toPure_548_; lean_object* v_a_549_; lean_object* v_b_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_toApplicative_546_ = lean_ctor_get(v_inst_503_, 0);
v_toBind_547_ = lean_ctor_get(v_inst_503_, 1);
lean_inc_n(v_toBind_547_, 2);
v_toPure_548_ = lean_ctor_get(v_toApplicative_546_, 1);
v_a_549_ = lean_ctor_get(v_a_509_, 0);
lean_inc_ref(v_a_549_);
v_b_550_ = lean_ctor_get(v_a_509_, 1);
lean_inc_ref(v_b_550_);
lean_dec_ref_known(v_a_509_, 2);
lean_inc_ref(v_inst_507_);
lean_inc_ref(v_inst_506_);
lean_inc(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_503_);
lean_inc(v_toPure_548_);
v___f_551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4), 11, 10);
lean_closure_set(v___f_551_, 0, v_toPure_548_);
lean_closure_set(v___f_551_, 1, v_inst_503_);
lean_closure_set(v___f_551_, 2, v_inst_504_);
lean_closure_set(v___f_551_, 3, v_inst_505_);
lean_closure_set(v___f_551_, 4, v_inst_506_);
lean_closure_set(v___f_551_, 5, v_inst_507_);
lean_closure_set(v___f_551_, 6, v_getVarExpr_508_);
lean_closure_set(v___f_551_, 7, v_b_550_);
lean_closure_set(v___f_551_, 8, v_toBind_547_);
lean_closure_set(v___f_551_, 9, v_a_549_);
v___x_552_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_505_, v_inst_504_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_553_ = lean_apply_4(v_toBind_547_, lean_box(0), lean_box(0), v___x_552_, v___f_551_);
return v___x_553_;
}
case 7:
{
lean_object* v_toApplicative_554_; lean_object* v_toBind_555_; lean_object* v_toPure_556_; lean_object* v_a_557_; lean_object* v_b_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_toApplicative_554_ = lean_ctor_get(v_inst_503_, 0);
v_toBind_555_ = lean_ctor_get(v_inst_503_, 1);
lean_inc_n(v_toBind_555_, 2);
v_toPure_556_ = lean_ctor_get(v_toApplicative_554_, 1);
v_a_557_ = lean_ctor_get(v_a_509_, 0);
lean_inc_ref(v_a_557_);
v_b_558_ = lean_ctor_get(v_a_509_, 1);
lean_inc_ref(v_b_558_);
lean_dec_ref_known(v_a_509_, 2);
lean_inc_ref(v_inst_507_);
lean_inc_ref(v_inst_506_);
lean_inc(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_503_);
lean_inc(v_toPure_556_);
v___f_559_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__4), 11, 10);
lean_closure_set(v___f_559_, 0, v_toPure_556_);
lean_closure_set(v___f_559_, 1, v_inst_503_);
lean_closure_set(v___f_559_, 2, v_inst_504_);
lean_closure_set(v___f_559_, 3, v_inst_505_);
lean_closure_set(v___f_559_, 4, v_inst_506_);
lean_closure_set(v___f_559_, 5, v_inst_507_);
lean_closure_set(v___f_559_, 6, v_getVarExpr_508_);
lean_closure_set(v___f_559_, 7, v_b_558_);
lean_closure_set(v___f_559_, 8, v_toBind_555_);
lean_closure_set(v___f_559_, 9, v_a_557_);
v___x_560_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_505_, v_inst_504_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_561_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v___x_560_, v___f_559_);
return v___x_561_;
}
default: 
{
lean_object* v_toApplicative_562_; lean_object* v_toBind_563_; lean_object* v_toPure_564_; lean_object* v_a_565_; lean_object* v_k_566_; lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_toApplicative_562_ = lean_ctor_get(v_inst_503_, 0);
v_toBind_563_ = lean_ctor_get(v_inst_503_, 1);
lean_inc_n(v_toBind_563_, 2);
v_toPure_564_ = lean_ctor_get(v_toApplicative_562_, 1);
v_a_565_ = lean_ctor_get(v_a_509_, 0);
lean_inc_ref(v_a_565_);
v_k_566_ = lean_ctor_get(v_a_509_, 1);
lean_inc(v_k_566_);
lean_dec_ref_known(v_a_509_, 2);
lean_inc_ref(v_inst_507_);
lean_inc_ref(v_inst_506_);
lean_inc(v_inst_505_);
lean_inc_ref(v_inst_504_);
lean_inc_ref(v_inst_503_);
lean_inc(v_toPure_564_);
v___f_567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__6), 11, 10);
lean_closure_set(v___f_567_, 0, v_k_566_);
lean_closure_set(v___f_567_, 1, v_toPure_564_);
lean_closure_set(v___f_567_, 2, v_inst_503_);
lean_closure_set(v___f_567_, 3, v_inst_504_);
lean_closure_set(v___f_567_, 4, v_inst_505_);
lean_closure_set(v___f_567_, 5, v_inst_506_);
lean_closure_set(v___f_567_, 6, v_inst_507_);
lean_closure_set(v___f_567_, 7, v_getVarExpr_508_);
lean_closure_set(v___f_567_, 8, v_a_565_);
lean_closure_set(v___f_567_, 9, v_toBind_563_);
v___x_568_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_505_, v_inst_504_, v_inst_503_, v_inst_506_, v_inst_507_);
v___x_569_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_568_, v___f_567_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__3(lean_object* v_toPure_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_getVarExpr_576_, lean_object* v_a_577_, lean_object* v_toBind_578_, lean_object* v_____do__lift_579_){
_start:
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___f_580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg___lam__2), 3, 2);
lean_closure_set(v___f_580_, 0, v_____do__lift_579_);
lean_closure_set(v___f_580_, 1, v_toPure_570_);
v___x_581_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_getVarExpr_576_, v_a_577_);
v___x_582_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_581_, v___f_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go(lean_object* v_m_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_getVarExpr_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_getVarExpr_589_, v_a_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore___redArg(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_getVarExpr_597_, lean_object* v_e_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_, v_getVarExpr_597_, v_e_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore(lean_object* v_m_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_getVarExpr_606_, lean_object* v_e_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_getVarExpr_606_, v_e_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(lean_object* v___x_609_, lean_object* v_vars_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_array_get_borrowed(v___x_609_, v_vars_610_, v_x_611_);
lean_inc(v___x_612_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed(lean_object* v___x_613_, lean_object* v_vars_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0(v___x_613_, v_vars_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec_ref(v_vars_614_);
lean_dec_ref(v___x_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_vars_622_, lean_object* v_e_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___f_625_; lean_object* v___x_626_; 
v___x_624_ = l_Lean_instInhabitedExpr;
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_625_, 0, v___x_624_);
lean_closure_set(v___f_625_, 1, v_vars_622_);
v___x_626_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteRingExprCore_go___redArg(v_inst_617_, v_inst_618_, v_inst_619_, v_inst_620_, v_inst_621_, v___f_625_, v_e_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteRingExpr(lean_object* v_m_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_vars_633_, lean_object* v_e_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Sym_Arith_denoteRingExpr___redArg(v_inst_628_, v_inst_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_vars_633_, v_e_634_);
return v___x_635_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
