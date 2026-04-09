// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_pp___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__0 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value;
static const lean_string_object l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__1 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value;
static const lean_ctor_object l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__2 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value;
static const lean_string_object l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__3 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value;
static const lean_string_object l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__4 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value;
static const lean_ctor_object l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Int_Linear_Poly_isNonlinear___redArg___closed__5 = (const lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Linear_Poly_normCommRing_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__0;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__1 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__1_value;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__2 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__2_value;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__3 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__3_value;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nonlinear"};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__4 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__4_value;
static const lean_ctor_object l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0),((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1),((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Int_Linear_Poly_normCommRing_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2),((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(51, 45, 160, 130, 43, 179, 195, 57)}};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__5 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__5_value;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__6 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__6_value;
static const lean_ctor_object l_Int_Linear_Poly_normCommRing_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__7 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__7_value;
static lean_once_cell_t l_Int_Linear_Poly_normCommRing_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__8;
static const lean_string_object l_Int_Linear_Poly_normCommRing_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " ===> "};
static const lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__9 = (const lean_object*)&l_Int_Linear_Poly_normCommRing_x3f___closed__9_value;
static lean_once_cell_t l_Int_Linear_Poly_normCommRing_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_normCommRing_x3f___closed__10;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___redArg(lean_object* v_p_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
if (lean_obj_tag(v_p_11_) == 1)
{
lean_object* v_v_15_; lean_object* v_p_16_; lean_object* v___x_17_; 
v_v_15_ = lean_ctor_get(v_p_11_, 1);
v_p_16_ = lean_ctor_get(v_p_11_, 2);
v___x_17_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_15_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_15_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_35_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_35_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_35_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_35_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = ((lean_object*)(l_Int_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_32_ = l_Lean_Expr_isAppOf(v_a_18_, v___x_31_);
lean_dec(v_a_18_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = ((lean_object*)(l_Int_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_34_ = l_Lean_Expr_isAppOf(v_a_20_, v___x_33_);
lean_dec(v_a_20_);
v___y_25_ = v___x_34_;
goto v___jp_24_;
}
else
{
lean_dec(v_a_20_);
v___y_25_ = v___x_32_;
goto v___jp_24_;
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_del_object(v___x_22_);
v_p_11_ = v_p_16_;
goto _start;
}
else
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = lean_box(v___y_25_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_27_);
v___x_29_ = v___x_22_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v_a_18_);
v_a_36_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_19_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_19_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
v_a_44_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_17_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_17_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
else
{
uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = 0;
v___x_53_ = lean_box(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___redArg___boxed(lean_object* v_p_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_55_, v_a_56_, v_a_57_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_p_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear(lean_object* v_p_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_60_, v_a_61_, v_a_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNonlinear___boxed(lean_object* v_p_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Int_Linear_Poly_isNonlinear(v_p_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_p_73_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
if (lean_obj_tag(v_a_86_) == 0)
{
lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_isSharedCheck_97_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_98_);
v___x_92_ = v_a_86_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_dec(v_a_86_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v_a_87_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_87_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v_v_99_; lean_object* v_p_100_; lean_object* v___x_101_; 
v_v_99_ = lean_ctor_get(v_a_86_, 1);
lean_inc(v_v_99_);
v_p_100_ = lean_ctor_get(v_a_86_, 2);
lean_inc_ref(v_p_100_);
lean_dec_ref(v_a_86_);
v___x_101_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_99_, v_a_88_, v_a_89_);
lean_dec(v_v_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_102_, v_a_88_);
lean_dec(v_a_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; uint8_t v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref(v___x_103_);
v___x_105_ = lean_nat_dec_le(v_a_104_, v_a_87_);
if (v___x_105_ == 0)
{
lean_dec(v_a_87_);
v_a_86_ = v_p_100_;
v_a_87_ = v_a_104_;
goto _start;
}
else
{
lean_dec(v_a_104_);
v_a_86_ = v_p_100_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_100_);
lean_dec(v_a_87_);
return v___x_103_;
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_p_100_);
lean_dec(v_a_87_);
v_a_108_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_101_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_101_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg___boxed(lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_122_, v_a_123_, v_a_124_, v_a_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___boxed(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec(v_a_138_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___redArg(lean_object* v_p_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_p_150_, v___x_154_, v_a_151_, v_a_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___redArg___boxed(lean_object* v_p_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_156_, v_a_157_, v_a_158_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration(lean_object* v_p_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_161_, v_a_162_, v_a_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getGeneration___boxed(lean_object* v_p_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_Linear_Poly_getGeneration(v_p_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec(v_a_175_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_191_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
v___x_200_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_199_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
return v___x_200_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_198_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___lam__0(uint8_t v_a_221_, lean_object* v_s_222_){
_start:
{
lean_object* v_vars_223_; lean_object* v_varMap_224_; lean_object* v_vars_x27_225_; lean_object* v_varMap_x27_226_; lean_object* v_natToIntMap_227_; lean_object* v_natDef_228_; lean_object* v_dvds_229_; lean_object* v_lowers_230_; lean_object* v_uppers_231_; lean_object* v_diseqs_232_; lean_object* v_elimEqs_233_; lean_object* v_elimStack_234_; lean_object* v_occurs_235_; lean_object* v_assignment_236_; lean_object* v_nextCnstrId_237_; uint8_t v_caseSplits_238_; lean_object* v_conflict_x3f_239_; lean_object* v_diseqSplits_240_; lean_object* v_divMod_241_; lean_object* v_toIntIds_242_; lean_object* v_toIntInfos_243_; lean_object* v_toIntTermMap_244_; lean_object* v_toIntVarMap_245_; lean_object* v_nonlinearOccs_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_vars_223_ = lean_ctor_get(v_s_222_, 0);
v_varMap_224_ = lean_ctor_get(v_s_222_, 1);
v_vars_x27_225_ = lean_ctor_get(v_s_222_, 2);
v_varMap_x27_226_ = lean_ctor_get(v_s_222_, 3);
v_natToIntMap_227_ = lean_ctor_get(v_s_222_, 4);
v_natDef_228_ = lean_ctor_get(v_s_222_, 5);
v_dvds_229_ = lean_ctor_get(v_s_222_, 6);
v_lowers_230_ = lean_ctor_get(v_s_222_, 7);
v_uppers_231_ = lean_ctor_get(v_s_222_, 8);
v_diseqs_232_ = lean_ctor_get(v_s_222_, 9);
v_elimEqs_233_ = lean_ctor_get(v_s_222_, 10);
v_elimStack_234_ = lean_ctor_get(v_s_222_, 11);
v_occurs_235_ = lean_ctor_get(v_s_222_, 12);
v_assignment_236_ = lean_ctor_get(v_s_222_, 13);
v_nextCnstrId_237_ = lean_ctor_get(v_s_222_, 14);
v_caseSplits_238_ = lean_ctor_get_uint8(v_s_222_, sizeof(void*)*23);
v_conflict_x3f_239_ = lean_ctor_get(v_s_222_, 15);
v_diseqSplits_240_ = lean_ctor_get(v_s_222_, 16);
v_divMod_241_ = lean_ctor_get(v_s_222_, 17);
v_toIntIds_242_ = lean_ctor_get(v_s_222_, 18);
v_toIntInfos_243_ = lean_ctor_get(v_s_222_, 19);
v_toIntTermMap_244_ = lean_ctor_get(v_s_222_, 20);
v_toIntVarMap_245_ = lean_ctor_get(v_s_222_, 21);
v_nonlinearOccs_246_ = lean_ctor_get(v_s_222_, 22);
v_isSharedCheck_253_ = !lean_is_exclusive(v_s_222_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v_s_222_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_nonlinearOccs_246_);
lean_inc(v_toIntVarMap_245_);
lean_inc(v_toIntTermMap_244_);
lean_inc(v_toIntInfos_243_);
lean_inc(v_toIntIds_242_);
lean_inc(v_divMod_241_);
lean_inc(v_diseqSplits_240_);
lean_inc(v_conflict_x3f_239_);
lean_inc(v_nextCnstrId_237_);
lean_inc(v_assignment_236_);
lean_inc(v_occurs_235_);
lean_inc(v_elimStack_234_);
lean_inc(v_elimEqs_233_);
lean_inc(v_diseqs_232_);
lean_inc(v_uppers_231_);
lean_inc(v_lowers_230_);
lean_inc(v_dvds_229_);
lean_inc(v_natDef_228_);
lean_inc(v_natToIntMap_227_);
lean_inc(v_varMap_x27_226_);
lean_inc(v_vars_x27_225_);
lean_inc(v_varMap_224_);
lean_inc(v_vars_223_);
lean_dec(v_s_222_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_vars_223_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_varMap_224_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_vars_x27_225_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_varMap_x27_226_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_natToIntMap_227_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_natDef_228_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_dvds_229_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_lowers_230_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_uppers_231_);
lean_ctor_set(v_reuseFailAlloc_252_, 9, v_diseqs_232_);
lean_ctor_set(v_reuseFailAlloc_252_, 10, v_elimEqs_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 11, v_elimStack_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 12, v_occurs_235_);
lean_ctor_set(v_reuseFailAlloc_252_, 13, v_assignment_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 14, v_nextCnstrId_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 15, v_conflict_x3f_239_);
lean_ctor_set(v_reuseFailAlloc_252_, 16, v_diseqSplits_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 17, v_divMod_241_);
lean_ctor_set(v_reuseFailAlloc_252_, 18, v_toIntIds_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 19, v_toIntInfos_243_);
lean_ctor_set(v_reuseFailAlloc_252_, 20, v_toIntTermMap_244_);
lean_ctor_set(v_reuseFailAlloc_252_, 21, v_toIntVarMap_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 22, v_nonlinearOccs_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*23, v_caseSplits_238_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*23 + 1, v_a_221_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_254_, lean_object* v_s_255_){
_start:
{
uint8_t v_a_152960__boxed_256_; lean_object* v_res_257_; 
v_a_152960__boxed_256_ = lean_unbox(v_a_254_);
v_res_257_ = l_Int_Linear_Poly_normCommRing_x3f___lam__0(v_a_152960__boxed_256_, v_s_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_258_, lean_object* v_s_259_){
_start:
{
lean_object* v_toRing_260_; lean_object* v_invFn_x3f_261_; lean_object* v_semiringId_x3f_262_; lean_object* v_commSemiringInst_263_; lean_object* v_commRingInst_264_; lean_object* v_noZeroDivInst_x3f_265_; lean_object* v_fieldInst_x3f_266_; lean_object* v_powIdentityInst_x3f_267_; lean_object* v_denoteEntries_268_; lean_object* v_nextId_269_; lean_object* v_steps_270_; lean_object* v_queue_271_; lean_object* v_basis_272_; lean_object* v_diseqs_273_; uint8_t v_recheck_274_; lean_object* v_invSet_275_; lean_object* v_powIdentityVarCount_276_; lean_object* v_numEq0_x3f_277_; uint8_t v_numEq0Updated_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_310_; 
v_toRing_260_ = lean_ctor_get(v_s_259_, 0);
v_invFn_x3f_261_ = lean_ctor_get(v_s_259_, 1);
v_semiringId_x3f_262_ = lean_ctor_get(v_s_259_, 2);
v_commSemiringInst_263_ = lean_ctor_get(v_s_259_, 3);
v_commRingInst_264_ = lean_ctor_get(v_s_259_, 4);
v_noZeroDivInst_x3f_265_ = lean_ctor_get(v_s_259_, 5);
v_fieldInst_x3f_266_ = lean_ctor_get(v_s_259_, 6);
v_powIdentityInst_x3f_267_ = lean_ctor_get(v_s_259_, 7);
v_denoteEntries_268_ = lean_ctor_get(v_s_259_, 8);
v_nextId_269_ = lean_ctor_get(v_s_259_, 9);
v_steps_270_ = lean_ctor_get(v_s_259_, 10);
v_queue_271_ = lean_ctor_get(v_s_259_, 11);
v_basis_272_ = lean_ctor_get(v_s_259_, 12);
v_diseqs_273_ = lean_ctor_get(v_s_259_, 13);
v_recheck_274_ = lean_ctor_get_uint8(v_s_259_, sizeof(void*)*17);
v_invSet_275_ = lean_ctor_get(v_s_259_, 14);
v_powIdentityVarCount_276_ = lean_ctor_get(v_s_259_, 15);
v_numEq0_x3f_277_ = lean_ctor_get(v_s_259_, 16);
v_numEq0Updated_278_ = lean_ctor_get_uint8(v_s_259_, sizeof(void*)*17 + 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_s_259_);
if (v_isSharedCheck_310_ == 0)
{
v___x_280_ = v_s_259_;
v_isShared_281_ = v_isSharedCheck_310_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_numEq0_x3f_277_);
lean_inc(v_powIdentityVarCount_276_);
lean_inc(v_invSet_275_);
lean_inc(v_diseqs_273_);
lean_inc(v_basis_272_);
lean_inc(v_queue_271_);
lean_inc(v_steps_270_);
lean_inc(v_nextId_269_);
lean_inc(v_denoteEntries_268_);
lean_inc(v_powIdentityInst_x3f_267_);
lean_inc(v_fieldInst_x3f_266_);
lean_inc(v_noZeroDivInst_x3f_265_);
lean_inc(v_commRingInst_264_);
lean_inc(v_commSemiringInst_263_);
lean_inc(v_semiringId_x3f_262_);
lean_inc(v_invFn_x3f_261_);
lean_inc(v_toRing_260_);
lean_dec(v_s_259_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_310_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_id_282_; lean_object* v_type_283_; lean_object* v_u_284_; lean_object* v_ringInst_285_; lean_object* v_semiringInst_286_; lean_object* v_charInst_x3f_287_; lean_object* v_addFn_x3f_288_; lean_object* v_mulFn_x3f_289_; lean_object* v_subFn_x3f_290_; lean_object* v_powFn_x3f_291_; lean_object* v_intCastFn_x3f_292_; lean_object* v_natCastFn_x3f_293_; lean_object* v_one_x3f_294_; lean_object* v_vars_295_; lean_object* v_varMap_296_; lean_object* v_denote_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_308_; 
v_id_282_ = lean_ctor_get(v_toRing_260_, 0);
v_type_283_ = lean_ctor_get(v_toRing_260_, 1);
v_u_284_ = lean_ctor_get(v_toRing_260_, 2);
v_ringInst_285_ = lean_ctor_get(v_toRing_260_, 3);
v_semiringInst_286_ = lean_ctor_get(v_toRing_260_, 4);
v_charInst_x3f_287_ = lean_ctor_get(v_toRing_260_, 5);
v_addFn_x3f_288_ = lean_ctor_get(v_toRing_260_, 6);
v_mulFn_x3f_289_ = lean_ctor_get(v_toRing_260_, 7);
v_subFn_x3f_290_ = lean_ctor_get(v_toRing_260_, 8);
v_powFn_x3f_291_ = lean_ctor_get(v_toRing_260_, 10);
v_intCastFn_x3f_292_ = lean_ctor_get(v_toRing_260_, 11);
v_natCastFn_x3f_293_ = lean_ctor_get(v_toRing_260_, 12);
v_one_x3f_294_ = lean_ctor_get(v_toRing_260_, 13);
v_vars_295_ = lean_ctor_get(v_toRing_260_, 14);
v_varMap_296_ = lean_ctor_get(v_toRing_260_, 15);
v_denote_297_ = lean_ctor_get(v_toRing_260_, 16);
v_isSharedCheck_308_ = !lean_is_exclusive(v_toRing_260_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v_toRing_260_, 9);
lean_dec(v_unused_309_);
v___x_299_ = v_toRing_260_;
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_denote_297_);
lean_inc(v_varMap_296_);
lean_inc(v_vars_295_);
lean_inc(v_one_x3f_294_);
lean_inc(v_natCastFn_x3f_293_);
lean_inc(v_intCastFn_x3f_292_);
lean_inc(v_powFn_x3f_291_);
lean_inc(v_subFn_x3f_290_);
lean_inc(v_mulFn_x3f_289_);
lean_inc(v_addFn_x3f_288_);
lean_inc(v_charInst_x3f_287_);
lean_inc(v_semiringInst_286_);
lean_inc(v_ringInst_285_);
lean_inc(v_u_284_);
lean_inc(v_type_283_);
lean_inc(v_id_282_);
lean_dec(v_toRing_260_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v_a_258_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 9, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_id_282_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_type_283_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_u_284_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_ringInst_285_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_semiringInst_286_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_charInst_x3f_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_addFn_x3f_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_mulFn_x3f_289_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_subFn_x3f_290_);
lean_ctor_set(v_reuseFailAlloc_307_, 9, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_307_, 10, v_powFn_x3f_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 11, v_intCastFn_x3f_292_);
lean_ctor_set(v_reuseFailAlloc_307_, 12, v_natCastFn_x3f_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 13, v_one_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_307_, 14, v_vars_295_);
lean_ctor_set(v_reuseFailAlloc_307_, 15, v_varMap_296_);
lean_ctor_set(v_reuseFailAlloc_307_, 16, v_denote_297_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_303_);
v___x_305_ = v___x_280_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_invFn_x3f_261_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_semiringId_x3f_262_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_commSemiringInst_263_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_commRingInst_264_);
lean_ctor_set(v_reuseFailAlloc_306_, 5, v_noZeroDivInst_x3f_265_);
lean_ctor_set(v_reuseFailAlloc_306_, 6, v_fieldInst_x3f_266_);
lean_ctor_set(v_reuseFailAlloc_306_, 7, v_powIdentityInst_x3f_267_);
lean_ctor_set(v_reuseFailAlloc_306_, 8, v_denoteEntries_268_);
lean_ctor_set(v_reuseFailAlloc_306_, 9, v_nextId_269_);
lean_ctor_set(v_reuseFailAlloc_306_, 10, v_steps_270_);
lean_ctor_set(v_reuseFailAlloc_306_, 11, v_queue_271_);
lean_ctor_set(v_reuseFailAlloc_306_, 12, v_basis_272_);
lean_ctor_set(v_reuseFailAlloc_306_, 13, v_diseqs_273_);
lean_ctor_set(v_reuseFailAlloc_306_, 14, v_invSet_275_);
lean_ctor_set(v_reuseFailAlloc_306_, 15, v_powIdentityVarCount_276_);
lean_ctor_set(v_reuseFailAlloc_306_, 16, v_numEq0_x3f_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*17, v_recheck_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*17 + 1, v_numEq0Updated_278_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v_mctx_320_; lean_object* v_lctx_321_; lean_object* v_options_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = lean_st_ref_get(v___y_313_);
v_mctx_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_mctx_320_);
lean_dec(v___x_319_);
v_lctx_321_ = lean_ctor_get(v___y_312_, 2);
v_options_322_ = lean_ctor_get(v___y_314_, 2);
lean_inc_ref(v_options_322_);
lean_inc_ref(v_lctx_321_);
v___x_323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_323_, 0, v_env_318_);
lean_ctor_set(v___x_323_, 1, v_mctx_320_);
lean_ctor_set(v___x_323_, 2, v_lctx_321_);
lean_ctor_set(v___x_323_, 3, v_options_322_);
v___x_324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_msgData_311_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_ref_339_; lean_object* v___x_340_; lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_ref_339_ = lean_ctor_get(v___y_336_, 5);
v___x_340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
lean_inc(v_ref_339_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_ref_339_);
lean_ctor_set(v___x_345_, 1, v_a_341_);
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 1);
lean_ctor_set(v___x_343_, 0, v___x_345_);
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
lean_inc_ref(v_type_360_);
v___x_373_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_360_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (lean_obj_tag(v_a_374_) == 1)
{
lean_object* v_val_378_; lean_object* v___x_380_; 
lean_dec_ref(v_type_360_);
v_val_378_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_378_);
lean_dec_ref(v_a_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_val_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_val_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_del_object(v___x_376_);
lean_dec(v_a_374_);
v___x_382_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_383_ = l_Lean_indentExpr(v_type_360_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_384_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_385_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_type_360_);
v_a_387_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_373_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_409_, lean_object* v_u_410_, lean_object* v_instDeclName_411_, lean_object* v_declName_412_, lean_object* v_expectedInst_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_427_, 0, v_u_410_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
lean_inc_ref(v___x_427_);
v___x_428_ = l_Lean_mkConst(v_instDeclName_411_, v___x_427_);
lean_inc_ref(v_type_409_);
v___x_429_ = l_Lean_Expr_app___override(v___x_428_, v_type_409_);
v___x_430_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_429_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_n(v_a_431_, 2);
lean_dec_ref(v___x_430_);
lean_inc(v_declName_412_);
v___x_432_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_412_, v_a_431_, v_expectedInst_413_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v___x_432_);
v___x_433_ = l_Lean_mkConst(v_declName_412_, v___x_427_);
v___x_434_ = l_Lean_mkAppB(v___x_433_, v_type_409_, v_a_431_);
v___x_435_ = l_Lean_Meta_Sym_canon(v___x_434_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
v___x_437_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_436_, v___y_420_);
return v___x_437_;
}
else
{
return v___x_435_;
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_a_431_);
lean_dec_ref(v___x_427_);
lean_dec(v_declName_412_);
lean_dec_ref(v_type_409_);
v_a_438_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_432_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_432_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
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
else
{
lean_dec_ref(v___x_427_);
lean_dec_ref(v_expectedInst_413_);
lean_dec(v_declName_412_);
lean_dec_ref(v_type_409_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_446_ = _args[0];
lean_object* v_u_447_ = _args[1];
lean_object* v_instDeclName_448_ = _args[2];
lean_object* v_declName_449_ = _args[3];
lean_object* v_expectedInst_450_ = _args[4];
lean_object* v___y_451_ = _args[5];
lean_object* v___y_452_ = _args[6];
lean_object* v___y_453_ = _args[7];
lean_object* v___y_454_ = _args[8];
lean_object* v___y_455_ = _args[9];
lean_object* v___y_456_ = _args[10];
lean_object* v___y_457_ = _args[11];
lean_object* v___y_458_ = _args[12];
lean_object* v___y_459_ = _args[13];
lean_object* v___y_460_ = _args[14];
lean_object* v___y_461_ = _args[15];
lean_object* v___y_462_ = _args[16];
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_446_, v_u_447_, v_instDeclName_448_, v_declName_449_, v_expectedInst_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_533_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_533_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_533_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_533_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_toRing_497_; lean_object* v_negFn_x3f_498_; 
v_toRing_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_toRing_497_);
lean_dec(v_a_493_);
v_negFn_x3f_498_ = lean_ctor_get(v_toRing_497_, 9);
if (lean_obj_tag(v_negFn_x3f_498_) == 1)
{
lean_object* v_val_499_; lean_object* v___x_501_; 
lean_inc_ref(v_negFn_x3f_498_);
lean_dec_ref(v_toRing_497_);
v_val_499_ = lean_ctor_get(v_negFn_x3f_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref(v_negFn_x3f_498_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_val_499_);
v___x_501_ = v___x_495_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_val_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_object* v_type_503_; lean_object* v_u_504_; lean_object* v_ringInst_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_expectedInst_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_495_);
v_type_503_ = lean_ctor_get(v_toRing_497_, 1);
lean_inc_ref_n(v_type_503_, 2);
v_u_504_ = lean_ctor_get(v_toRing_497_, 2);
lean_inc_n(v_u_504_, 2);
v_ringInst_505_ = lean_ctor_get(v_toRing_497_, 3);
lean_inc_ref(v_ringInst_505_);
lean_dec_ref(v_toRing_497_);
v___x_506_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_u_504_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_mkConst(v___x_506_, v___x_508_);
v_expectedInst_510_ = l_Lean_mkAppB(v___x_509_, v_type_503_, v_ringInst_505_);
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8));
v___x_513_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_503_, v_u_504_, v___x_511_, v___x_512_, v_expectedInst_510_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_n(v_a_514_, 2);
lean_dec_ref(v___x_513_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_515_, 0, v_a_514_);
v___x_516_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_515_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_516_, 0);
lean_dec(v_unused_524_);
v___x_518_ = v___x_516_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_dec(v___x_516_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_a_514_);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_514_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_514_);
v_a_525_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_516_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_492_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_492_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_nat_to_int(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_toRing_585_; lean_object* v_type_586_; lean_object* v_u_587_; lean_object* v_semiringInst_588_; lean_object* v___x_589_; lean_object* v_n_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_583_);
v_toRing_585_ = lean_ctor_get(v_a_584_, 0);
lean_inc_ref(v_toRing_585_);
lean_dec(v_a_584_);
v_type_586_ = lean_ctor_get(v_toRing_585_, 1);
lean_inc_ref_n(v_type_586_, 2);
v_u_587_ = lean_ctor_get(v_toRing_585_, 2);
lean_inc(v_u_587_);
v_semiringInst_588_ = lean_ctor_get(v_toRing_585_, 4);
lean_inc_ref(v_semiringInst_588_);
lean_dec_ref(v_toRing_585_);
v___x_589_ = lean_nat_abs(v_k_570_);
v_n_590_ = l_Lean_mkRawNatLit(v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v_u_587_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_inc_ref(v___x_593_);
v___x_594_ = l_Lean_mkConst(v___x_591_, v___x_593_);
lean_inc_ref(v_n_590_);
v___x_595_ = l_Lean_mkAppB(v___x_594_, v_type_586_, v_n_590_);
v___x_596_ = lean_box(0);
v___x_597_ = l_Lean_Meta_synthInstance_x3f(v___x_595_, v___x_596_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_637_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_637_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_637_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_637_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_ofNatInst_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; 
if (lean_obj_tag(v_a_598_) == 1)
{
lean_object* v_val_633_; 
lean_dec_ref(v_semiringInst_588_);
v_val_633_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_val_633_);
lean_dec_ref(v_a_598_);
v_ofNatInst_603_ = v_val_633_;
v___y_604_ = v___y_571_;
v___y_605_ = v___y_572_;
v___y_606_ = v___y_573_;
v___y_607_ = v___y_574_;
v___y_608_ = v___y_575_;
v___y_609_ = v___y_576_;
v___y_610_ = v___y_577_;
v___y_611_ = v___y_578_;
v___y_612_ = v___y_579_;
v___y_613_ = v___y_580_;
v___y_614_ = v___y_581_;
goto v___jp_602_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_a_598_);
v___x_634_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6));
lean_inc_ref(v___x_593_);
v___x_635_ = l_Lean_mkConst(v___x_634_, v___x_593_);
lean_inc_ref(v_n_590_);
lean_inc_ref(v_type_586_);
v___x_636_ = l_Lean_mkApp3(v___x_635_, v_type_586_, v_semiringInst_588_, v_n_590_);
v_ofNatInst_603_ = v___x_636_;
v___y_604_ = v___y_571_;
v___y_605_ = v___y_572_;
v___y_606_ = v___y_573_;
v___y_607_ = v___y_574_;
v___y_608_ = v___y_575_;
v___y_609_ = v___y_576_;
v___y_610_ = v___y_577_;
v___y_611_ = v___y_578_;
v___y_612_ = v___y_579_;
v___y_613_ = v___y_580_;
v___y_614_ = v___y_581_;
goto v___jp_602_;
}
v___jp_602_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_n_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_593_);
v_n_617_ = l_Lean_mkApp3(v___x_616_, v_type_586_, v_n_590_, v_ofNatInst_603_);
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_619_ = lean_int_dec_lt(v_k_570_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_621_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_n_617_);
v___x_621_ = v___x_600_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_n_617_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; 
lean_del_object(v___x_600_);
v___x_623_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = l_Lean_Expr_app___override(v_a_624_, v_n_617_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_dec_ref(v_n_617_);
return v___x_623_;
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v___x_593_);
lean_dec_ref(v_n_590_);
lean_dec_ref(v_semiringInst_588_);
lean_dec_ref(v_type_586_);
v_a_638_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_597_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_597_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_a_646_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_583_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_583_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v_k_654_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_668_, lean_object* v_s_669_){
_start:
{
lean_object* v_toRing_670_; lean_object* v_invFn_x3f_671_; lean_object* v_semiringId_x3f_672_; lean_object* v_commSemiringInst_673_; lean_object* v_commRingInst_674_; lean_object* v_noZeroDivInst_x3f_675_; lean_object* v_fieldInst_x3f_676_; lean_object* v_powIdentityInst_x3f_677_; lean_object* v_denoteEntries_678_; lean_object* v_nextId_679_; lean_object* v_steps_680_; lean_object* v_queue_681_; lean_object* v_basis_682_; lean_object* v_diseqs_683_; uint8_t v_recheck_684_; lean_object* v_invSet_685_; lean_object* v_powIdentityVarCount_686_; lean_object* v_numEq0_x3f_687_; uint8_t v_numEq0Updated_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_720_; 
v_toRing_670_ = lean_ctor_get(v_s_669_, 0);
v_invFn_x3f_671_ = lean_ctor_get(v_s_669_, 1);
v_semiringId_x3f_672_ = lean_ctor_get(v_s_669_, 2);
v_commSemiringInst_673_ = lean_ctor_get(v_s_669_, 3);
v_commRingInst_674_ = lean_ctor_get(v_s_669_, 4);
v_noZeroDivInst_x3f_675_ = lean_ctor_get(v_s_669_, 5);
v_fieldInst_x3f_676_ = lean_ctor_get(v_s_669_, 6);
v_powIdentityInst_x3f_677_ = lean_ctor_get(v_s_669_, 7);
v_denoteEntries_678_ = lean_ctor_get(v_s_669_, 8);
v_nextId_679_ = lean_ctor_get(v_s_669_, 9);
v_steps_680_ = lean_ctor_get(v_s_669_, 10);
v_queue_681_ = lean_ctor_get(v_s_669_, 11);
v_basis_682_ = lean_ctor_get(v_s_669_, 12);
v_diseqs_683_ = lean_ctor_get(v_s_669_, 13);
v_recheck_684_ = lean_ctor_get_uint8(v_s_669_, sizeof(void*)*17);
v_invSet_685_ = lean_ctor_get(v_s_669_, 14);
v_powIdentityVarCount_686_ = lean_ctor_get(v_s_669_, 15);
v_numEq0_x3f_687_ = lean_ctor_get(v_s_669_, 16);
v_numEq0Updated_688_ = lean_ctor_get_uint8(v_s_669_, sizeof(void*)*17 + 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_s_669_);
if (v_isSharedCheck_720_ == 0)
{
v___x_690_ = v_s_669_;
v_isShared_691_ = v_isSharedCheck_720_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_numEq0_x3f_687_);
lean_inc(v_powIdentityVarCount_686_);
lean_inc(v_invSet_685_);
lean_inc(v_diseqs_683_);
lean_inc(v_basis_682_);
lean_inc(v_queue_681_);
lean_inc(v_steps_680_);
lean_inc(v_nextId_679_);
lean_inc(v_denoteEntries_678_);
lean_inc(v_powIdentityInst_x3f_677_);
lean_inc(v_fieldInst_x3f_676_);
lean_inc(v_noZeroDivInst_x3f_675_);
lean_inc(v_commRingInst_674_);
lean_inc(v_commSemiringInst_673_);
lean_inc(v_semiringId_x3f_672_);
lean_inc(v_invFn_x3f_671_);
lean_inc(v_toRing_670_);
lean_dec(v_s_669_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_720_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_id_692_; lean_object* v_type_693_; lean_object* v_u_694_; lean_object* v_ringInst_695_; lean_object* v_semiringInst_696_; lean_object* v_charInst_x3f_697_; lean_object* v_mulFn_x3f_698_; lean_object* v_subFn_x3f_699_; lean_object* v_negFn_x3f_700_; lean_object* v_powFn_x3f_701_; lean_object* v_intCastFn_x3f_702_; lean_object* v_natCastFn_x3f_703_; lean_object* v_one_x3f_704_; lean_object* v_vars_705_; lean_object* v_varMap_706_; lean_object* v_denote_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_718_; 
v_id_692_ = lean_ctor_get(v_toRing_670_, 0);
v_type_693_ = lean_ctor_get(v_toRing_670_, 1);
v_u_694_ = lean_ctor_get(v_toRing_670_, 2);
v_ringInst_695_ = lean_ctor_get(v_toRing_670_, 3);
v_semiringInst_696_ = lean_ctor_get(v_toRing_670_, 4);
v_charInst_x3f_697_ = lean_ctor_get(v_toRing_670_, 5);
v_mulFn_x3f_698_ = lean_ctor_get(v_toRing_670_, 7);
v_subFn_x3f_699_ = lean_ctor_get(v_toRing_670_, 8);
v_negFn_x3f_700_ = lean_ctor_get(v_toRing_670_, 9);
v_powFn_x3f_701_ = lean_ctor_get(v_toRing_670_, 10);
v_intCastFn_x3f_702_ = lean_ctor_get(v_toRing_670_, 11);
v_natCastFn_x3f_703_ = lean_ctor_get(v_toRing_670_, 12);
v_one_x3f_704_ = lean_ctor_get(v_toRing_670_, 13);
v_vars_705_ = lean_ctor_get(v_toRing_670_, 14);
v_varMap_706_ = lean_ctor_get(v_toRing_670_, 15);
v_denote_707_ = lean_ctor_get(v_toRing_670_, 16);
v_isSharedCheck_718_ = !lean_is_exclusive(v_toRing_670_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_toRing_670_, 6);
lean_dec(v_unused_719_);
v___x_709_ = v_toRing_670_;
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_denote_707_);
lean_inc(v_varMap_706_);
lean_inc(v_vars_705_);
lean_inc(v_one_x3f_704_);
lean_inc(v_natCastFn_x3f_703_);
lean_inc(v_intCastFn_x3f_702_);
lean_inc(v_powFn_x3f_701_);
lean_inc(v_negFn_x3f_700_);
lean_inc(v_subFn_x3f_699_);
lean_inc(v_mulFn_x3f_698_);
lean_inc(v_charInst_x3f_697_);
lean_inc(v_semiringInst_696_);
lean_inc(v_ringInst_695_);
lean_inc(v_u_694_);
lean_inc(v_type_693_);
lean_inc(v_id_692_);
lean_dec(v_toRing_670_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_a_668_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 6, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_id_692_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_type_693_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_u_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_ringInst_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_semiringInst_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_charInst_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_mulFn_x3f_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_subFn_x3f_699_);
lean_ctor_set(v_reuseFailAlloc_717_, 9, v_negFn_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_717_, 10, v_powFn_x3f_701_);
lean_ctor_set(v_reuseFailAlloc_717_, 11, v_intCastFn_x3f_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 12, v_natCastFn_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 13, v_one_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 14, v_vars_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 15, v_varMap_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 16, v_denote_707_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_713_);
v___x_715_ = v___x_690_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_invFn_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_semiringId_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_commSemiringInst_673_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_commRingInst_674_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_noZeroDivInst_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_fieldInst_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_powIdentityInst_x3f_677_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v_denoteEntries_678_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v_nextId_679_);
lean_ctor_set(v_reuseFailAlloc_716_, 10, v_steps_680_);
lean_ctor_set(v_reuseFailAlloc_716_, 11, v_queue_681_);
lean_ctor_set(v_reuseFailAlloc_716_, 12, v_basis_682_);
lean_ctor_set(v_reuseFailAlloc_716_, 13, v_diseqs_683_);
lean_ctor_set(v_reuseFailAlloc_716_, 14, v_invSet_685_);
lean_ctor_set(v_reuseFailAlloc_716_, 15, v_powIdentityVarCount_686_);
lean_ctor_set(v_reuseFailAlloc_716_, 16, v_numEq0_x3f_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_716_, sizeof(void*)*17, v_recheck_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_716_, sizeof(void*)*17 + 1, v_numEq0Updated_688_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_721_, lean_object* v_u_722_, lean_object* v_instDeclName_723_, lean_object* v_declName_724_, lean_object* v_expectedInst_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_738_ = lean_box(0);
lean_inc_n(v_u_722_, 2);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_u_722_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_u_722_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v_u_722_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
lean_inc_ref(v___x_741_);
v___x_742_ = l_Lean_mkConst(v_instDeclName_723_, v___x_741_);
lean_inc_ref_n(v_type_721_, 3);
v___x_743_ = l_Lean_mkApp3(v___x_742_, v_type_721_, v_type_721_, v_type_721_);
v___x_744_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_743_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_n(v_a_745_, 2);
lean_dec_ref(v___x_744_);
lean_inc(v_declName_724_);
v___x_746_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_724_, v_a_745_, v_expectedInst_725_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___x_746_);
v___x_747_ = l_Lean_mkConst(v_declName_724_, v___x_741_);
lean_inc_ref_n(v_type_721_, 2);
v___x_748_ = l_Lean_mkApp4(v___x_747_, v_type_721_, v_type_721_, v_type_721_, v_a_745_);
v___x_749_ = l_Lean_Meta_Sym_canon(v___x_748_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v___x_751_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_750_, v___y_732_);
return v___x_751_;
}
else
{
return v___x_749_;
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_745_);
lean_dec_ref(v___x_741_);
lean_dec(v_declName_724_);
lean_dec_ref(v_type_721_);
v_a_752_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_746_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_746_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_dec_ref(v___x_741_);
lean_dec_ref(v_expectedInst_725_);
lean_dec(v_declName_724_);
lean_dec_ref(v_type_721_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_760_ = _args[0];
lean_object* v_u_761_ = _args[1];
lean_object* v_instDeclName_762_ = _args[2];
lean_object* v_declName_763_ = _args[3];
lean_object* v_expectedInst_764_ = _args[4];
lean_object* v___y_765_ = _args[5];
lean_object* v___y_766_ = _args[6];
lean_object* v___y_767_ = _args[7];
lean_object* v___y_768_ = _args[8];
lean_object* v___y_769_ = _args[9];
lean_object* v___y_770_ = _args[10];
lean_object* v___y_771_ = _args[11];
lean_object* v___y_772_ = _args[12];
lean_object* v___y_773_ = _args[13];
lean_object* v___y_774_ = _args[14];
lean_object* v___y_775_ = _args[15];
lean_object* v___y_776_ = _args[16];
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_760_, v_u_761_, v_instDeclName_762_, v_declName_763_, v_expectedInst_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_850_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_850_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_850_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_850_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_toRing_811_; lean_object* v_addFn_x3f_812_; 
v_toRing_811_ = lean_ctor_get(v_a_807_, 0);
lean_inc_ref(v_toRing_811_);
lean_dec(v_a_807_);
v_addFn_x3f_812_ = lean_ctor_get(v_toRing_811_, 6);
if (lean_obj_tag(v_addFn_x3f_812_) == 1)
{
lean_object* v_val_813_; lean_object* v___x_815_; 
lean_inc_ref(v_addFn_x3f_812_);
lean_dec_ref(v_toRing_811_);
v_val_813_ = lean_ctor_get(v_addFn_x3f_812_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_addFn_x3f_812_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v_val_813_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v_type_817_; lean_object* v_u_818_; lean_object* v_semiringInst_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_expectedInst_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_809_);
v_type_817_ = lean_ctor_get(v_toRing_811_, 1);
lean_inc_ref_n(v_type_817_, 3);
v_u_818_ = lean_ctor_get(v_toRing_811_, 2);
lean_inc_n(v_u_818_, 2);
v_semiringInst_819_ = lean_ctor_get(v_toRing_811_, 4);
lean_inc_ref(v_semiringInst_819_);
lean_dec_ref(v_toRing_811_);
v___x_820_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v_u_818_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
lean_inc_ref(v___x_822_);
v___x_823_ = l_Lean_mkConst(v___x_820_, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3));
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_822_);
v___x_826_ = l_Lean_mkAppB(v___x_825_, v_type_817_, v_semiringInst_819_);
v_expectedInst_827_ = l_Lean_mkAppB(v___x_823_, v_type_817_, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5));
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7));
v___x_830_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_817_, v_u_818_, v___x_828_, v___x_829_, v_expectedInst_827_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___f_832_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_n(v_a_831_, 2);
lean_dec_ref(v___x_830_);
v___f_832_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_832_, 0, v_a_831_);
v___x_833_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_832_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_841_);
v___x_835_ = v___x_833_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_dec(v___x_833_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_a_831_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_831_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_831_);
v_a_842_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_833_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_833_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_806_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_806_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_872_, lean_object* v_s_873_){
_start:
{
lean_object* v_toRing_874_; lean_object* v_invFn_x3f_875_; lean_object* v_semiringId_x3f_876_; lean_object* v_commSemiringInst_877_; lean_object* v_commRingInst_878_; lean_object* v_noZeroDivInst_x3f_879_; lean_object* v_fieldInst_x3f_880_; lean_object* v_powIdentityInst_x3f_881_; lean_object* v_denoteEntries_882_; lean_object* v_nextId_883_; lean_object* v_steps_884_; lean_object* v_queue_885_; lean_object* v_basis_886_; lean_object* v_diseqs_887_; uint8_t v_recheck_888_; lean_object* v_invSet_889_; lean_object* v_powIdentityVarCount_890_; lean_object* v_numEq0_x3f_891_; uint8_t v_numEq0Updated_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_924_; 
v_toRing_874_ = lean_ctor_get(v_s_873_, 0);
v_invFn_x3f_875_ = lean_ctor_get(v_s_873_, 1);
v_semiringId_x3f_876_ = lean_ctor_get(v_s_873_, 2);
v_commSemiringInst_877_ = lean_ctor_get(v_s_873_, 3);
v_commRingInst_878_ = lean_ctor_get(v_s_873_, 4);
v_noZeroDivInst_x3f_879_ = lean_ctor_get(v_s_873_, 5);
v_fieldInst_x3f_880_ = lean_ctor_get(v_s_873_, 6);
v_powIdentityInst_x3f_881_ = lean_ctor_get(v_s_873_, 7);
v_denoteEntries_882_ = lean_ctor_get(v_s_873_, 8);
v_nextId_883_ = lean_ctor_get(v_s_873_, 9);
v_steps_884_ = lean_ctor_get(v_s_873_, 10);
v_queue_885_ = lean_ctor_get(v_s_873_, 11);
v_basis_886_ = lean_ctor_get(v_s_873_, 12);
v_diseqs_887_ = lean_ctor_get(v_s_873_, 13);
v_recheck_888_ = lean_ctor_get_uint8(v_s_873_, sizeof(void*)*17);
v_invSet_889_ = lean_ctor_get(v_s_873_, 14);
v_powIdentityVarCount_890_ = lean_ctor_get(v_s_873_, 15);
v_numEq0_x3f_891_ = lean_ctor_get(v_s_873_, 16);
v_numEq0Updated_892_ = lean_ctor_get_uint8(v_s_873_, sizeof(void*)*17 + 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_s_873_);
if (v_isSharedCheck_924_ == 0)
{
v___x_894_ = v_s_873_;
v_isShared_895_ = v_isSharedCheck_924_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_numEq0_x3f_891_);
lean_inc(v_powIdentityVarCount_890_);
lean_inc(v_invSet_889_);
lean_inc(v_diseqs_887_);
lean_inc(v_basis_886_);
lean_inc(v_queue_885_);
lean_inc(v_steps_884_);
lean_inc(v_nextId_883_);
lean_inc(v_denoteEntries_882_);
lean_inc(v_powIdentityInst_x3f_881_);
lean_inc(v_fieldInst_x3f_880_);
lean_inc(v_noZeroDivInst_x3f_879_);
lean_inc(v_commRingInst_878_);
lean_inc(v_commSemiringInst_877_);
lean_inc(v_semiringId_x3f_876_);
lean_inc(v_invFn_x3f_875_);
lean_inc(v_toRing_874_);
lean_dec(v_s_873_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_924_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_id_896_; lean_object* v_type_897_; lean_object* v_u_898_; lean_object* v_ringInst_899_; lean_object* v_semiringInst_900_; lean_object* v_charInst_x3f_901_; lean_object* v_addFn_x3f_902_; lean_object* v_subFn_x3f_903_; lean_object* v_negFn_x3f_904_; lean_object* v_powFn_x3f_905_; lean_object* v_intCastFn_x3f_906_; lean_object* v_natCastFn_x3f_907_; lean_object* v_one_x3f_908_; lean_object* v_vars_909_; lean_object* v_varMap_910_; lean_object* v_denote_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_922_; 
v_id_896_ = lean_ctor_get(v_toRing_874_, 0);
v_type_897_ = lean_ctor_get(v_toRing_874_, 1);
v_u_898_ = lean_ctor_get(v_toRing_874_, 2);
v_ringInst_899_ = lean_ctor_get(v_toRing_874_, 3);
v_semiringInst_900_ = lean_ctor_get(v_toRing_874_, 4);
v_charInst_x3f_901_ = lean_ctor_get(v_toRing_874_, 5);
v_addFn_x3f_902_ = lean_ctor_get(v_toRing_874_, 6);
v_subFn_x3f_903_ = lean_ctor_get(v_toRing_874_, 8);
v_negFn_x3f_904_ = lean_ctor_get(v_toRing_874_, 9);
v_powFn_x3f_905_ = lean_ctor_get(v_toRing_874_, 10);
v_intCastFn_x3f_906_ = lean_ctor_get(v_toRing_874_, 11);
v_natCastFn_x3f_907_ = lean_ctor_get(v_toRing_874_, 12);
v_one_x3f_908_ = lean_ctor_get(v_toRing_874_, 13);
v_vars_909_ = lean_ctor_get(v_toRing_874_, 14);
v_varMap_910_ = lean_ctor_get(v_toRing_874_, 15);
v_denote_911_ = lean_ctor_get(v_toRing_874_, 16);
v_isSharedCheck_922_ = !lean_is_exclusive(v_toRing_874_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_toRing_874_, 7);
lean_dec(v_unused_923_);
v___x_913_ = v_toRing_874_;
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_denote_911_);
lean_inc(v_varMap_910_);
lean_inc(v_vars_909_);
lean_inc(v_one_x3f_908_);
lean_inc(v_natCastFn_x3f_907_);
lean_inc(v_intCastFn_x3f_906_);
lean_inc(v_powFn_x3f_905_);
lean_inc(v_negFn_x3f_904_);
lean_inc(v_subFn_x3f_903_);
lean_inc(v_addFn_x3f_902_);
lean_inc(v_charInst_x3f_901_);
lean_inc(v_semiringInst_900_);
lean_inc(v_ringInst_899_);
lean_inc(v_u_898_);
lean_inc(v_type_897_);
lean_inc(v_id_896_);
lean_dec(v_toRing_874_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_a_872_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 7, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_id_896_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_type_897_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_u_898_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_ringInst_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_semiringInst_900_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v_charInst_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_addFn_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_subFn_x3f_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 9, v_negFn_x3f_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 10, v_powFn_x3f_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 11, v_intCastFn_x3f_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 12, v_natCastFn_x3f_907_);
lean_ctor_set(v_reuseFailAlloc_921_, 13, v_one_x3f_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 14, v_vars_909_);
lean_ctor_set(v_reuseFailAlloc_921_, 15, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_921_, 16, v_denote_911_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_917_);
v___x_919_ = v___x_894_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_invFn_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_semiringId_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_commSemiringInst_877_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_commRingInst_878_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_noZeroDivInst_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_920_, 6, v_fieldInst_x3f_880_);
lean_ctor_set(v_reuseFailAlloc_920_, 7, v_powIdentityInst_x3f_881_);
lean_ctor_set(v_reuseFailAlloc_920_, 8, v_denoteEntries_882_);
lean_ctor_set(v_reuseFailAlloc_920_, 9, v_nextId_883_);
lean_ctor_set(v_reuseFailAlloc_920_, 10, v_steps_884_);
lean_ctor_set(v_reuseFailAlloc_920_, 11, v_queue_885_);
lean_ctor_set(v_reuseFailAlloc_920_, 12, v_basis_886_);
lean_ctor_set(v_reuseFailAlloc_920_, 13, v_diseqs_887_);
lean_ctor_set(v_reuseFailAlloc_920_, 14, v_invSet_889_);
lean_ctor_set(v_reuseFailAlloc_920_, 15, v_powIdentityVarCount_890_);
lean_ctor_set(v_reuseFailAlloc_920_, 16, v_numEq0_x3f_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*17, v_recheck_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*17 + 1, v_numEq0Updated_892_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_992_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_992_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_992_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_992_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_toRing_953_; lean_object* v_mulFn_x3f_954_; 
v_toRing_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc_ref(v_toRing_953_);
lean_dec(v_a_949_);
v_mulFn_x3f_954_ = lean_ctor_get(v_toRing_953_, 7);
if (lean_obj_tag(v_mulFn_x3f_954_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; 
lean_inc_ref(v_mulFn_x3f_954_);
lean_dec_ref(v_toRing_953_);
v_val_955_ = lean_ctor_get(v_mulFn_x3f_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref(v_mulFn_x3f_954_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_val_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v_type_959_; lean_object* v_u_960_; lean_object* v_semiringInst_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_expectedInst_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_del_object(v___x_951_);
v_type_959_ = lean_ctor_get(v_toRing_953_, 1);
lean_inc_ref_n(v_type_959_, 3);
v_u_960_ = lean_ctor_get(v_toRing_953_, 2);
lean_inc_n(v_u_960_, 2);
v_semiringInst_961_ = lean_ctor_get(v_toRing_953_, 4);
lean_inc_ref(v_semiringInst_961_);
lean_dec_ref(v_toRing_953_);
v___x_962_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v_u_960_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_inc_ref(v___x_964_);
v___x_965_ = l_Lean_mkConst(v___x_962_, v___x_964_);
v___x_966_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_967_ = l_Lean_mkConst(v___x_966_, v___x_964_);
v___x_968_ = l_Lean_mkAppB(v___x_967_, v_type_959_, v_semiringInst_961_);
v_expectedInst_969_ = l_Lean_mkAppB(v___x_965_, v_type_959_, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_971_ = ((lean_object*)(l_Int_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_972_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_959_, v_u_960_, v___x_970_, v___x_971_, v_expectedInst_969_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___f_974_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_n(v_a_973_, 2);
lean_dec_ref(v___x_972_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_974_, 0, v_a_973_);
v___x_975_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_974_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_983_);
v___x_977_ = v___x_975_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_975_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_a_973_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_973_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_973_);
v_a_984_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_975_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_975_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_948_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_948_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_1014_, lean_object* v_s_1015_){
_start:
{
lean_object* v_toRing_1016_; lean_object* v_invFn_x3f_1017_; lean_object* v_semiringId_x3f_1018_; lean_object* v_commSemiringInst_1019_; lean_object* v_commRingInst_1020_; lean_object* v_noZeroDivInst_x3f_1021_; lean_object* v_fieldInst_x3f_1022_; lean_object* v_powIdentityInst_x3f_1023_; lean_object* v_denoteEntries_1024_; lean_object* v_nextId_1025_; lean_object* v_steps_1026_; lean_object* v_queue_1027_; lean_object* v_basis_1028_; lean_object* v_diseqs_1029_; uint8_t v_recheck_1030_; lean_object* v_invSet_1031_; lean_object* v_powIdentityVarCount_1032_; lean_object* v_numEq0_x3f_1033_; uint8_t v_numEq0Updated_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1066_; 
v_toRing_1016_ = lean_ctor_get(v_s_1015_, 0);
v_invFn_x3f_1017_ = lean_ctor_get(v_s_1015_, 1);
v_semiringId_x3f_1018_ = lean_ctor_get(v_s_1015_, 2);
v_commSemiringInst_1019_ = lean_ctor_get(v_s_1015_, 3);
v_commRingInst_1020_ = lean_ctor_get(v_s_1015_, 4);
v_noZeroDivInst_x3f_1021_ = lean_ctor_get(v_s_1015_, 5);
v_fieldInst_x3f_1022_ = lean_ctor_get(v_s_1015_, 6);
v_powIdentityInst_x3f_1023_ = lean_ctor_get(v_s_1015_, 7);
v_denoteEntries_1024_ = lean_ctor_get(v_s_1015_, 8);
v_nextId_1025_ = lean_ctor_get(v_s_1015_, 9);
v_steps_1026_ = lean_ctor_get(v_s_1015_, 10);
v_queue_1027_ = lean_ctor_get(v_s_1015_, 11);
v_basis_1028_ = lean_ctor_get(v_s_1015_, 12);
v_diseqs_1029_ = lean_ctor_get(v_s_1015_, 13);
v_recheck_1030_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*17);
v_invSet_1031_ = lean_ctor_get(v_s_1015_, 14);
v_powIdentityVarCount_1032_ = lean_ctor_get(v_s_1015_, 15);
v_numEq0_x3f_1033_ = lean_ctor_get(v_s_1015_, 16);
v_numEq0Updated_1034_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*17 + 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_s_1015_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1036_ = v_s_1015_;
v_isShared_1037_ = v_isSharedCheck_1066_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_numEq0_x3f_1033_);
lean_inc(v_powIdentityVarCount_1032_);
lean_inc(v_invSet_1031_);
lean_inc(v_diseqs_1029_);
lean_inc(v_basis_1028_);
lean_inc(v_queue_1027_);
lean_inc(v_steps_1026_);
lean_inc(v_nextId_1025_);
lean_inc(v_denoteEntries_1024_);
lean_inc(v_powIdentityInst_x3f_1023_);
lean_inc(v_fieldInst_x3f_1022_);
lean_inc(v_noZeroDivInst_x3f_1021_);
lean_inc(v_commRingInst_1020_);
lean_inc(v_commSemiringInst_1019_);
lean_inc(v_semiringId_x3f_1018_);
lean_inc(v_invFn_x3f_1017_);
lean_inc(v_toRing_1016_);
lean_dec(v_s_1015_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1066_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_id_1038_; lean_object* v_type_1039_; lean_object* v_u_1040_; lean_object* v_ringInst_1041_; lean_object* v_semiringInst_1042_; lean_object* v_charInst_x3f_1043_; lean_object* v_addFn_x3f_1044_; lean_object* v_mulFn_x3f_1045_; lean_object* v_subFn_x3f_1046_; lean_object* v_negFn_x3f_1047_; lean_object* v_intCastFn_x3f_1048_; lean_object* v_natCastFn_x3f_1049_; lean_object* v_one_x3f_1050_; lean_object* v_vars_1051_; lean_object* v_varMap_1052_; lean_object* v_denote_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1064_; 
v_id_1038_ = lean_ctor_get(v_toRing_1016_, 0);
v_type_1039_ = lean_ctor_get(v_toRing_1016_, 1);
v_u_1040_ = lean_ctor_get(v_toRing_1016_, 2);
v_ringInst_1041_ = lean_ctor_get(v_toRing_1016_, 3);
v_semiringInst_1042_ = lean_ctor_get(v_toRing_1016_, 4);
v_charInst_x3f_1043_ = lean_ctor_get(v_toRing_1016_, 5);
v_addFn_x3f_1044_ = lean_ctor_get(v_toRing_1016_, 6);
v_mulFn_x3f_1045_ = lean_ctor_get(v_toRing_1016_, 7);
v_subFn_x3f_1046_ = lean_ctor_get(v_toRing_1016_, 8);
v_negFn_x3f_1047_ = lean_ctor_get(v_toRing_1016_, 9);
v_intCastFn_x3f_1048_ = lean_ctor_get(v_toRing_1016_, 11);
v_natCastFn_x3f_1049_ = lean_ctor_get(v_toRing_1016_, 12);
v_one_x3f_1050_ = lean_ctor_get(v_toRing_1016_, 13);
v_vars_1051_ = lean_ctor_get(v_toRing_1016_, 14);
v_varMap_1052_ = lean_ctor_get(v_toRing_1016_, 15);
v_denote_1053_ = lean_ctor_get(v_toRing_1016_, 16);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_toRing_1016_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_toRing_1016_, 10);
lean_dec(v_unused_1065_);
v___x_1055_ = v_toRing_1016_;
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_denote_1053_);
lean_inc(v_varMap_1052_);
lean_inc(v_vars_1051_);
lean_inc(v_one_x3f_1050_);
lean_inc(v_natCastFn_x3f_1049_);
lean_inc(v_intCastFn_x3f_1048_);
lean_inc(v_negFn_x3f_1047_);
lean_inc(v_subFn_x3f_1046_);
lean_inc(v_mulFn_x3f_1045_);
lean_inc(v_addFn_x3f_1044_);
lean_inc(v_charInst_x3f_1043_);
lean_inc(v_semiringInst_1042_);
lean_inc(v_ringInst_1041_);
lean_inc(v_u_1040_);
lean_inc(v_type_1039_);
lean_inc(v_id_1038_);
lean_dec(v_toRing_1016_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1014_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 10, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_id_1038_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_type_1039_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_u_1040_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_ringInst_1041_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_semiringInst_1042_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_charInst_x3f_1043_);
lean_ctor_set(v_reuseFailAlloc_1063_, 6, v_addFn_x3f_1044_);
lean_ctor_set(v_reuseFailAlloc_1063_, 7, v_mulFn_x3f_1045_);
lean_ctor_set(v_reuseFailAlloc_1063_, 8, v_subFn_x3f_1046_);
lean_ctor_set(v_reuseFailAlloc_1063_, 9, v_negFn_x3f_1047_);
lean_ctor_set(v_reuseFailAlloc_1063_, 10, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1063_, 11, v_intCastFn_x3f_1048_);
lean_ctor_set(v_reuseFailAlloc_1063_, 12, v_natCastFn_x3f_1049_);
lean_ctor_set(v_reuseFailAlloc_1063_, 13, v_one_x3f_1050_);
lean_ctor_set(v_reuseFailAlloc_1063_, 14, v_vars_1051_);
lean_ctor_set(v_reuseFailAlloc_1063_, 15, v_varMap_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 16, v_denote_1053_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1059_);
v___x_1061_ = v___x_1036_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_invFn_x3f_1017_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_semiringId_x3f_1018_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_commSemiringInst_1019_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_commRingInst_1020_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v_noZeroDivInst_x3f_1021_);
lean_ctor_set(v_reuseFailAlloc_1062_, 6, v_fieldInst_x3f_1022_);
lean_ctor_set(v_reuseFailAlloc_1062_, 7, v_powIdentityInst_x3f_1023_);
lean_ctor_set(v_reuseFailAlloc_1062_, 8, v_denoteEntries_1024_);
lean_ctor_set(v_reuseFailAlloc_1062_, 9, v_nextId_1025_);
lean_ctor_set(v_reuseFailAlloc_1062_, 10, v_steps_1026_);
lean_ctor_set(v_reuseFailAlloc_1062_, 11, v_queue_1027_);
lean_ctor_set(v_reuseFailAlloc_1062_, 12, v_basis_1028_);
lean_ctor_set(v_reuseFailAlloc_1062_, 13, v_diseqs_1029_);
lean_ctor_set(v_reuseFailAlloc_1062_, 14, v_invSet_1031_);
lean_ctor_set(v_reuseFailAlloc_1062_, 15, v_powIdentityVarCount_1032_);
lean_ctor_set(v_reuseFailAlloc_1062_, 16, v_numEq0_x3f_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*17, v_recheck_1030_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*17 + 1, v_numEq0Updated_1034_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Lean_Level_ofNat(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_1077_, lean_object* v_type_1078_, lean_object* v_semiringInst_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_1094_ = lean_box(0);
lean_inc(v_u_1077_);
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_u_1077_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_u_1077_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_inc_ref(v___x_1097_);
v___x_1098_ = l_Lean_mkConst(v___x_1092_, v___x_1097_);
v___x_1099_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_1078_, 2);
v___x_1100_ = l_Lean_mkApp3(v___x_1098_, v_type_1078_, v___x_1099_, v_type_1078_);
v___x_1101_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_1100_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_inst_x27_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_n(v_a_1102_, 2);
lean_dec_ref(v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_1104_ = l_Lean_mkConst(v___x_1103_, v___x_1095_);
lean_inc_ref(v_type_1078_);
v_inst_x27_1105_ = l_Lean_mkAppB(v___x_1104_, v_type_1078_, v_semiringInst_1079_);
v___x_1106_ = ((lean_object*)(l_Int_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_1107_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_1106_, v_a_1102_, v_inst_x27_1105_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec_ref(v___x_1107_);
v___x_1108_ = l_Lean_mkConst(v___x_1106_, v___x_1097_);
lean_inc_ref(v_type_1078_);
v___x_1109_ = l_Lean_mkApp4(v___x_1108_, v_type_1078_, v___x_1099_, v_type_1078_, v_a_1102_);
v___x_1110_ = l_Lean_Meta_Sym_canon(v___x_1109_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1111_, v___y_1086_);
return v___x_1112_;
}
else
{
return v___x_1110_;
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1102_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_type_1078_);
v_a_1113_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1107_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1107_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_semiringInst_1079_);
lean_dec_ref(v_type_1078_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_1121_, lean_object* v_type_1122_, lean_object* v_semiringInst_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1121_, v_type_1122_, v_semiringInst_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1183_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_toRing_1154_; lean_object* v_powFn_x3f_1155_; 
v_toRing_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc_ref(v_toRing_1154_);
lean_dec(v_a_1150_);
v_powFn_x3f_1155_ = lean_ctor_get(v_toRing_1154_, 10);
if (lean_obj_tag(v_powFn_x3f_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1158_; 
lean_inc_ref(v_powFn_x3f_1155_);
lean_dec_ref(v_toRing_1154_);
v_val_1156_ = lean_ctor_get(v_powFn_x3f_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref(v_powFn_x3f_1155_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_val_1156_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_val_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v_type_1160_; lean_object* v_u_1161_; lean_object* v_semiringInst_1162_; lean_object* v___x_1163_; 
lean_del_object(v___x_1152_);
v_type_1160_ = lean_ctor_get(v_toRing_1154_, 1);
lean_inc_ref(v_type_1160_);
v_u_1161_ = lean_ctor_get(v_toRing_1154_, 2);
lean_inc(v_u_1161_);
v_semiringInst_1162_ = lean_ctor_get(v_toRing_1154_, 4);
lean_inc_ref(v_semiringInst_1162_);
lean_dec_ref(v_toRing_1154_);
v___x_1163_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1161_, v_type_1160_, v_semiringInst_1162_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc_n(v_a_1164_, 2);
lean_dec_ref(v___x_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1165_, 0, v_a_1164_);
v___x_1166_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1165_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v___x_1166_, 0);
lean_dec(v_unused_1174_);
v___x_1168_ = v___x_1166_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v___x_1166_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_a_1164_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1164_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1164_);
v_a_1175_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1149_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1149_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1250_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_toRing_1223_; lean_object* v_vars_1224_; lean_object* v_x_1225_; lean_object* v_k_1226_; lean_object* v___y_1228_; lean_object* v_size_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_toRing_1223_ = lean_ctor_get(v_a_1219_, 0);
lean_inc_ref(v_toRing_1223_);
lean_dec(v_a_1219_);
v_vars_1224_ = lean_ctor_get(v_toRing_1223_, 14);
lean_inc_ref(v_vars_1224_);
lean_dec_ref(v_toRing_1223_);
v_x_1225_ = lean_ctor_get(v_pw_1205_, 0);
lean_inc(v_x_1225_);
v_k_1226_ = lean_ctor_get(v_pw_1205_, 1);
lean_inc(v_k_1226_);
lean_dec_ref(v_pw_1205_);
v_size_1245_ = lean_ctor_get(v_vars_1224_, 2);
v___x_1246_ = l_Lean_instInhabitedExpr;
v___x_1247_ = lean_nat_dec_lt(v_x_1225_, v_size_1245_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
lean_dec(v_x_1225_);
lean_dec_ref(v_vars_1224_);
v___x_1248_ = l_outOfBounds___redArg(v___x_1246_);
v___y_1228_ = v___x_1248_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1246_, v_vars_1224_, v_x_1225_);
lean_dec(v_x_1225_);
lean_dec_ref(v_vars_1224_);
v___y_1228_ = v___x_1249_;
goto v___jp_1227_;
}
v___jp_1227_:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_dec_eq(v_k_1226_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_del_object(v___x_1221_);
v___x_1231_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1241_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_mkNatLit(v_k_1226_);
v___x_1237_ = l_Lean_mkAppB(v_a_1232_, v___y_1228_, v___x_1236_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_dec_ref(v___y_1228_);
lean_dec(v_k_1226_);
return v___x_1231_;
}
}
else
{
lean_object* v___x_1243_; 
lean_dec(v_k_1226_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___y_1228_);
v___x_1243_ = v___x_1221_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___y_1228_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_pw_1205_);
v_a_1251_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1218_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1218_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_m_1273_, lean_object* v_acc_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
if (lean_obj_tag(v_m_1273_) == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_acc_1274_);
return v___x_1287_;
}
else
{
lean_object* v_p_1288_; lean_object* v_m_1289_; lean_object* v___x_1290_; 
v_p_1288_ = lean_ctor_get(v_m_1273_, 0);
lean_inc_ref(v_p_1288_);
v_m_1289_ = lean_ctor_get(v_m_1273_, 1);
lean_inc(v_m_1289_);
lean_dec_ref(v_m_1273_);
v___x_1290_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v___x_1290_);
v___x_1292_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = l_Lean_mkAppB(v_a_1291_, v_acc_1274_, v_a_1293_);
v_m_1273_ = v_m_1289_;
v_acc_1274_ = v___x_1294_;
goto _start;
}
else
{
lean_dec(v_a_1291_);
lean_dec(v_m_1289_);
lean_dec_ref(v_acc_1274_);
return v___x_1292_;
}
}
else
{
lean_dec(v_m_1289_);
lean_dec_ref(v_p_1288_);
lean_dec_ref(v_acc_1274_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_m_1296_, lean_object* v_acc_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1296_, v_acc_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1310_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_to_int(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_m_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
if (lean_obj_tag(v_m_1313_) == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1327_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1326_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1327_;
}
else
{
lean_object* v_p_1328_; lean_object* v_m_1329_; lean_object* v___x_1330_; 
v_p_1328_ = lean_ctor_get(v_m_1313_, 0);
lean_inc_ref(v_p_1328_);
v_m_1329_ = lean_ctor_get(v_m_1313_, 1);
lean_inc(v_m_1329_);
lean_dec_ref(v_m_1313_);
v___x_1330_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1328_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1329_, v_a_1331_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1332_;
}
else
{
lean_dec(v_m_1329_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_m_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1347_, lean_object* v_m_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1362_ = lean_int_dec_eq(v_k_1347_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Lean_mkAppB(v_a_1364_, v_a_1366_, v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_dec(v_a_1366_);
lean_dec(v_a_1364_);
return v___x_1367_;
}
}
else
{
lean_dec(v_a_1364_);
lean_dec(v_m_1348_);
return v___x_1365_;
}
}
else
{
lean_dec(v_m_1348_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1378_, lean_object* v_m_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1378_, v_m_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v_k_1378_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1393_, lean_object* v_acc_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
if (lean_obj_tag(v_p_1393_) == 0)
{
lean_object* v_k_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1428_; 
v_k_1407_ = lean_ctor_get(v_p_1393_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_p_1393_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1409_ = v_p_1393_;
v_isShared_1410_ = v_isSharedCheck_1428_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_k_1407_);
lean_dec(v_p_1393_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1428_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1412_ = lean_int_dec_eq(v_k_1407_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_del_object(v___x_1409_);
v___x_1413_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1407_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v_k_1407_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lean_mkAppB(v_a_1414_, v_acc_1394_, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_dec(v_a_1414_);
lean_dec_ref(v_acc_1394_);
return v___x_1415_;
}
}
else
{
lean_dec(v_k_1407_);
lean_dec_ref(v_acc_1394_);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_k_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v_acc_1394_);
v___x_1426_ = v___x_1409_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_acc_1394_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_p_1431_; lean_object* v___x_1432_; 
v_k_1429_ = lean_ctor_get(v_p_1393_, 0);
lean_inc(v_k_1429_);
v_v_1430_ = lean_ctor_get(v_p_1393_, 1);
lean_inc(v_v_1430_);
v_p_1431_ = lean_ctor_get(v_p_1393_, 2);
lean_inc_ref(v_p_1431_);
lean_dec_ref(v_p_1393_);
v___x_1432_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1429_, v_v_1430_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v_k_1429_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = l_Lean_mkAppB(v_a_1433_, v_acc_1394_, v_a_1435_);
v_p_1393_ = v_p_1431_;
v_acc_1394_ = v___x_1436_;
goto _start;
}
else
{
lean_dec(v_a_1433_);
lean_dec_ref(v_p_1431_);
lean_dec_ref(v_acc_1394_);
return v___x_1434_;
}
}
else
{
lean_dec_ref(v_p_1431_);
lean_dec(v_v_1430_);
lean_dec(v_k_1429_);
lean_dec_ref(v_acc_1394_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1438_, lean_object* v_acc_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1438_, v_acc_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
if (lean_obj_tag(v_p_1453_) == 0)
{
lean_object* v_k_1466_; lean_object* v___x_1467_; 
v_k_1466_ = lean_ctor_get(v_p_1453_, 0);
lean_inc(v_k_1466_);
lean_dec_ref(v_p_1453_);
v___x_1467_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1466_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v_k_1466_);
return v___x_1467_;
}
else
{
lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v_p_1470_; lean_object* v___x_1471_; 
v_k_1468_ = lean_ctor_get(v_p_1453_, 0);
lean_inc(v_k_1468_);
v_v_1469_ = lean_ctor_get(v_p_1453_, 1);
lean_inc(v_v_1469_);
v_p_1470_ = lean_ctor_get(v_p_1453_, 2);
lean_inc_ref(v_p_1470_);
lean_dec_ref(v_p_1453_);
v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1468_, v_v_1469_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v_k_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1470_, v_a_1472_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_p_1470_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(v_p_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1487_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1488_; double v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_float_of_nat(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1546_; 
v_ref_1500_ = lean_ctor_get(v___y_1497_, 5);
v___x_1501_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1546_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1546_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v_traceState_1507_; lean_object* v_env_1508_; lean_object* v_nextMacroScope_1509_; lean_object* v_ngen_1510_; lean_object* v_auxDeclNGen_1511_; lean_object* v_cache_1512_; lean_object* v_messages_1513_; lean_object* v_infoState_1514_; lean_object* v_snapshotTasks_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1545_; 
v___x_1506_ = lean_st_ref_take(v___y_1498_);
v_traceState_1507_ = lean_ctor_get(v___x_1506_, 4);
v_env_1508_ = lean_ctor_get(v___x_1506_, 0);
v_nextMacroScope_1509_ = lean_ctor_get(v___x_1506_, 1);
v_ngen_1510_ = lean_ctor_get(v___x_1506_, 2);
v_auxDeclNGen_1511_ = lean_ctor_get(v___x_1506_, 3);
v_cache_1512_ = lean_ctor_get(v___x_1506_, 5);
v_messages_1513_ = lean_ctor_get(v___x_1506_, 6);
v_infoState_1514_ = lean_ctor_get(v___x_1506_, 7);
v_snapshotTasks_1515_ = lean_ctor_get(v___x_1506_, 8);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1517_ = v___x_1506_;
v_isShared_1518_ = v_isSharedCheck_1545_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snapshotTasks_1515_);
lean_inc(v_infoState_1514_);
lean_inc(v_messages_1513_);
lean_inc(v_cache_1512_);
lean_inc(v_traceState_1507_);
lean_inc(v_auxDeclNGen_1511_);
lean_inc(v_ngen_1510_);
lean_inc(v_nextMacroScope_1509_);
lean_inc(v_env_1508_);
lean_dec(v___x_1506_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1545_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
uint64_t v_tid_1519_; lean_object* v_traces_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1544_; 
v_tid_1519_ = lean_ctor_get_uint64(v_traceState_1507_, sizeof(void*)*1);
v_traces_1520_ = lean_ctor_get(v_traceState_1507_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_traceState_1507_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1522_ = v_traceState_1507_;
v_isShared_1523_ = v_isSharedCheck_1544_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_traces_1520_);
lean_dec(v_traceState_1507_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1544_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; double v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_float_once(&l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1526_ = 0;
v___x_1527_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1528_, 0, v_cls_1493_);
lean_ctor_set(v___x_1528_, 1, v___x_1524_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
lean_ctor_set_float(v___x_1528_, sizeof(void*)*3, v___x_1525_);
lean_ctor_set_float(v___x_1528_, sizeof(void*)*3 + 8, v___x_1525_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*3 + 16, v___x_1526_);
v___x_1529_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1530_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v_a_1502_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
lean_inc(v_ref_1500_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_ref_1500_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_PersistentArray_push___redArg(v_traces_1520_, v___x_1531_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1532_);
v___x_1534_ = v___x_1522_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1532_);
lean_ctor_set_uint64(v_reuseFailAlloc_1543_, sizeof(void*)*1, v_tid_1519_);
v___x_1534_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 4, v___x_1534_);
v___x_1536_ = v___x_1517_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_env_1508_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_nextMacroScope_1509_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_ngen_1510_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_auxDeclNGen_1511_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v_cache_1512_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_messages_1513_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_infoState_1514_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_snapshotTasks_1515_);
v___x_1536_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = lean_st_ref_set(v___y_1498_, v___x_1536_);
v___x_1538_ = lean_box(0);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1538_);
v___x_1540_ = v___x_1504_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1547_, lean_object* v_msg_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1547_, v_msg_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1554_;
}
}
static lean_object* _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Int_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((lean_object*)(l_Int_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1570_ = ((lean_object*)(l_Int_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1571_ = l_Lean_Name_append(v___x_1570_, v___x_1569_);
return v___x_1571_;
}
}
static lean_object* _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Int_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object* v_p_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1813_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1813_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1813_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_unbox(v_a_1588_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v___x_1593_ = lean_box(0);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v___x_1597_; 
lean_del_object(v___x_1590_);
v___x_1597_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1804_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1804_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1804_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
if (lean_obj_tag(v_a_1598_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1600_);
v_val_1602_ = lean_ctor_get(v_a_1598_, 0);
lean_inc(v_val_1602_);
lean_dec_ref(v_a_1598_);
lean_inc_ref(v_p_1575_);
v___x_1603_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_Lean_Meta_Sym_canon(v_a_1604_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1606_, v_a_1581_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1607_);
lean_inc_ref(v_p_1575_);
v___x_1609_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_n(v_a_1610_, 2);
lean_dec_ref(v___x_1609_);
v___x_1611_ = 0;
v___x_1612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1612_, 0, v_val_1602_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = lean_unbox(v_a_1588_);
v___x_1614_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1608_, v___x_1613_, v_a_1610_, v___x_1612_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1759_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1759_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1759_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
if (lean_obj_tag(v_a_1615_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1620_; 
lean_del_object(v___x_1617_);
v_val_1619_ = lean_ctor_get(v_a_1615_, 0);
lean_inc_n(v_val_1619_, 2);
lean_dec_ref(v_a_1615_);
v___x_1620_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_val_1619_, v___x_1612_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1746_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1746_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1746_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
if (lean_obj_tag(v_a_1621_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1741_; 
lean_del_object(v___x_1623_);
v_val_1625_ = lean_ctor_get(v_a_1621_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_a_1621_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1627_ = v_a_1621_;
v_isShared_1628_ = v_isSharedCheck_1741_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v_a_1621_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1741_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; 
lean_inc(v_val_1625_);
v___x_1629_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(v_val_1625_, v___x_1612_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec_ref(v___x_1612_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1630_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc_n(v_a_1632_, 2);
lean_dec_ref(v___x_1631_);
v___x_1633_ = lean_obj_once(&l_Int_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc(v_a_1576_);
v___x_1634_ = lean_grind_internalize(v_a_1632_, v_a_1610_, v___x_1633_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1715_; 
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1716_);
v___x_1636_ = v___x_1634_;
v_isShared_1637_ = v_isSharedCheck_1715_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v___x_1634_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1715_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1632_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1706_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1706_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1706_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Int_Linear_instBEqPoly_beq(v_p_1575_, v_a_1639_);
if (v___x_1652_ == 0)
{
lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_del_object(v___x_1636_);
v___f_1653_ = lean_alloc_closure((void*)(l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1653_, 0, v_a_1588_);
v___x_1654_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1654_, v___f_1653_, v_a_1576_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_options_1656_; uint8_t v_hasTrace_1657_; 
lean_dec_ref(v___x_1655_);
v_options_1656_ = lean_ctor_get(v_a_1584_, 2);
v_hasTrace_1657_ = lean_ctor_get_uint8(v_options_1656_, sizeof(void*)*1);
if (v_hasTrace_1657_ == 0)
{
lean_dec_ref(v_p_1575_);
goto v___jp_1643_;
}
else
{
lean_object* v_inheritedTraceOptions_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_inheritedTraceOptions_1658_ = lean_ctor_get(v_a_1584_, 13);
v___x_1659_ = ((lean_object*)(l_Int_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1660_ = lean_obj_once(&l_Int_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1658_, v_options_1656_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v_p_1575_);
goto v___jp_1643_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Int_Linear_Poly_pp___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref(v___x_1662_);
lean_inc(v_a_1639_);
v___x_1664_ = l_Int_Linear_Poly_pp___redArg(v_a_1639_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = lean_obj_once(&l_Int_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_a_1663_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_a_1665_);
v___x_1669_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1659_, v___x_1668_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_dec_ref(v___x_1669_);
goto v___jp_1643_;
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1663_);
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
v_a_1678_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1664_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1664_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
v_a_1686_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1662_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1662_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec_ref(v_p_1575_);
v_a_1694_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1655_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1655_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v___x_1702_ = lean_box(0);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1702_);
v___x_1704_ = v___x_1636_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
v___jp_1643_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_val_1625_);
lean_ctor_set(v___x_1644_, 1, v_a_1639_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_val_1619_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1645_);
v___x_1647_ = v___x_1627_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1647_);
v___x_1649_ = v___x_1641_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_del_object(v___x_1636_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1707_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1638_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1638_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1632_);
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1717_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1634_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1634_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1725_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1631_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1631_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_del_object(v___x_1627_);
lean_dec(v_val_1625_);
lean_dec(v_val_1619_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1733_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1629_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1629_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec(v_a_1621_);
lean_dec(v_val_1619_);
lean_dec_ref(v___x_1612_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v___x_1742_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1742_);
v___x_1744_ = v___x_1623_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_val_1619_);
lean_dec_ref(v___x_1612_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1747_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1620_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1620_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec(v_a_1615_);
lean_dec_ref(v___x_1612_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v___x_1755_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1755_);
v___x_1757_ = v___x_1617_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v___x_1612_);
lean_dec(v_a_1610_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1760_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1614_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1614_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_a_1608_);
lean_dec(v_val_1602_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1768_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1609_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1609_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_val_1602_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1776_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1607_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1607_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_val_1602_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1784_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1605_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1605_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_val_1602_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1792_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1603_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1603_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_a_1598_);
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v___x_1800_ = lean_box(0);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1800_);
v___x_1802_ = v___x_1600_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1588_);
lean_dec_ref(v_p_1575_);
v_a_1805_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1597_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1597_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_p_1575_);
v_a_1814_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1587_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1587_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec(v_a_1823_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1835_, v_msg_1836_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1850_, v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1865_, lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1866_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1880_, v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1894_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
}
#ifdef __cplusplus
}
#endif
