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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0_value;
static const lean_string_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__1 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__1_value;
static const lean_ctor_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2_value;
static const lean_string_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3_value;
static const lean_string_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__4 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__4_value;
static const lean_ctor_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5 = (const lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__1 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__1_value;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__2 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__2_value;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__3 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__3_value;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nonlinear"};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__4 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__4_value;
static const lean_ctor_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0),((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1),((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2),((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(51, 45, 160, 130, 43, 179, 195, 57)}};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5_value;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__6 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__6_value;
static const lean_ctor_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8;
static const lean_string_object l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " ===> "};
static const lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9 = (const lean_object*)&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg(lean_object* v_p_11_, lean_object* v_a_12_, lean_object* v_a_13_){
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
lean_dec_ref_known(v___x_17_, 1);
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
v___x_31_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_32_ = l_Lean_Expr_isAppOf(v_a_18_, v___x_31_);
lean_dec(v_a_18_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___boxed(lean_object* v_p_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_55_, v_a_56_, v_a_57_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_p_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear(lean_object* v_p_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_60_, v_a_61_, v_a_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___boxed(lean_object* v_p_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Int_Internal_Linear_Poly_isNonlinear(v_p_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
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
lean_dec_ref_known(v_a_86_, 3);
v___x_101_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_99_, v_a_88_, v_a_89_);
lean_dec(v_v_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_102_, v_a_88_);
lean_dec(v_a_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; uint8_t v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg___boxed(lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_a_122_, v_a_123_, v_a_124_, v_a_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___boxed(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg(lean_object* v_p_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_p_150_, v___x_154_, v_a_151_, v_a_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg___boxed(lean_object* v_p_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_156_, v_a_157_, v_a_158_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration(lean_object* v_p_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_161_, v_a_162_, v_a_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___boxed(lean_object* v_p_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_Internal_Linear_Poly_getGeneration(v_p_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
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
lean_dec_ref_known(v___x_198_, 1);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(uint8_t v_a_221_, lean_object* v_s_222_){
_start:
{
lean_object* v_vars_223_; lean_object* v_varMap_224_; lean_object* v_vars_x27_225_; lean_object* v_varMap_x27_226_; lean_object* v_natToIntMap_227_; lean_object* v_natDef_228_; lean_object* v_dvds_229_; lean_object* v_lowers_230_; lean_object* v_uppers_231_; lean_object* v_diseqs_232_; lean_object* v_elimEqs_233_; lean_object* v_elimStack_234_; lean_object* v_occurs_235_; lean_object* v_assignment_236_; lean_object* v_nextCnstrId_237_; uint8_t v_caseSplits_238_; lean_object* v_steps_239_; lean_object* v_conflict_x3f_240_; lean_object* v_diseqSplits_241_; lean_object* v_divMod_242_; lean_object* v_nonlinearOccs_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
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
v_caseSplits_238_ = lean_ctor_get_uint8(v_s_222_, sizeof(void*)*20);
v_steps_239_ = lean_ctor_get(v_s_222_, 15);
v_conflict_x3f_240_ = lean_ctor_get(v_s_222_, 16);
v_diseqSplits_241_ = lean_ctor_get(v_s_222_, 17);
v_divMod_242_ = lean_ctor_get(v_s_222_, 18);
v_nonlinearOccs_243_ = lean_ctor_get(v_s_222_, 19);
v_isSharedCheck_250_ = !lean_is_exclusive(v_s_222_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v_s_222_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_nonlinearOccs_243_);
lean_inc(v_divMod_242_);
lean_inc(v_diseqSplits_241_);
lean_inc(v_conflict_x3f_240_);
lean_inc(v_steps_239_);
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
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_vars_223_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_varMap_224_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_vars_x27_225_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_varMap_x27_226_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_natToIntMap_227_);
lean_ctor_set(v_reuseFailAlloc_249_, 5, v_natDef_228_);
lean_ctor_set(v_reuseFailAlloc_249_, 6, v_dvds_229_);
lean_ctor_set(v_reuseFailAlloc_249_, 7, v_lowers_230_);
lean_ctor_set(v_reuseFailAlloc_249_, 8, v_uppers_231_);
lean_ctor_set(v_reuseFailAlloc_249_, 9, v_diseqs_232_);
lean_ctor_set(v_reuseFailAlloc_249_, 10, v_elimEqs_233_);
lean_ctor_set(v_reuseFailAlloc_249_, 11, v_elimStack_234_);
lean_ctor_set(v_reuseFailAlloc_249_, 12, v_occurs_235_);
lean_ctor_set(v_reuseFailAlloc_249_, 13, v_assignment_236_);
lean_ctor_set(v_reuseFailAlloc_249_, 14, v_nextCnstrId_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 15, v_steps_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 16, v_conflict_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 17, v_diseqSplits_241_);
lean_ctor_set(v_reuseFailAlloc_249_, 18, v_divMod_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 19, v_nonlinearOccs_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*20, v_caseSplits_238_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*20 + 1, v_a_221_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_251_, lean_object* v_s_252_){
_start:
{
uint8_t v_a_128281__boxed_253_; lean_object* v_res_254_; 
v_a_128281__boxed_253_ = lean_unbox(v_a_251_);
v_res_254_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_128281__boxed_253_, v_s_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_255_, lean_object* v_s_256_){
_start:
{
lean_object* v_toRing_257_; lean_object* v_invFn_x3f_258_; lean_object* v_semiringId_x3f_259_; lean_object* v_commSemiringInst_260_; lean_object* v_commRingInst_261_; lean_object* v_noZeroDivInst_x3f_262_; lean_object* v_fieldInst_x3f_263_; lean_object* v_powIdentityInst_x3f_264_; lean_object* v_denoteEntries_265_; lean_object* v_nextId_266_; lean_object* v_steps_267_; lean_object* v_queue_268_; lean_object* v_basis_269_; lean_object* v_diseqs_270_; uint8_t v_recheck_271_; lean_object* v_invSet_272_; lean_object* v_powIdentityVarCount_273_; lean_object* v_numEq0_x3f_274_; uint8_t v_numEq0Updated_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_307_; 
v_toRing_257_ = lean_ctor_get(v_s_256_, 0);
v_invFn_x3f_258_ = lean_ctor_get(v_s_256_, 1);
v_semiringId_x3f_259_ = lean_ctor_get(v_s_256_, 2);
v_commSemiringInst_260_ = lean_ctor_get(v_s_256_, 3);
v_commRingInst_261_ = lean_ctor_get(v_s_256_, 4);
v_noZeroDivInst_x3f_262_ = lean_ctor_get(v_s_256_, 5);
v_fieldInst_x3f_263_ = lean_ctor_get(v_s_256_, 6);
v_powIdentityInst_x3f_264_ = lean_ctor_get(v_s_256_, 7);
v_denoteEntries_265_ = lean_ctor_get(v_s_256_, 8);
v_nextId_266_ = lean_ctor_get(v_s_256_, 9);
v_steps_267_ = lean_ctor_get(v_s_256_, 10);
v_queue_268_ = lean_ctor_get(v_s_256_, 11);
v_basis_269_ = lean_ctor_get(v_s_256_, 12);
v_diseqs_270_ = lean_ctor_get(v_s_256_, 13);
v_recheck_271_ = lean_ctor_get_uint8(v_s_256_, sizeof(void*)*17);
v_invSet_272_ = lean_ctor_get(v_s_256_, 14);
v_powIdentityVarCount_273_ = lean_ctor_get(v_s_256_, 15);
v_numEq0_x3f_274_ = lean_ctor_get(v_s_256_, 16);
v_numEq0Updated_275_ = lean_ctor_get_uint8(v_s_256_, sizeof(void*)*17 + 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_s_256_);
if (v_isSharedCheck_307_ == 0)
{
v___x_277_ = v_s_256_;
v_isShared_278_ = v_isSharedCheck_307_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_numEq0_x3f_274_);
lean_inc(v_powIdentityVarCount_273_);
lean_inc(v_invSet_272_);
lean_inc(v_diseqs_270_);
lean_inc(v_basis_269_);
lean_inc(v_queue_268_);
lean_inc(v_steps_267_);
lean_inc(v_nextId_266_);
lean_inc(v_denoteEntries_265_);
lean_inc(v_powIdentityInst_x3f_264_);
lean_inc(v_fieldInst_x3f_263_);
lean_inc(v_noZeroDivInst_x3f_262_);
lean_inc(v_commRingInst_261_);
lean_inc(v_commSemiringInst_260_);
lean_inc(v_semiringId_x3f_259_);
lean_inc(v_invFn_x3f_258_);
lean_inc(v_toRing_257_);
lean_dec(v_s_256_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_307_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_id_279_; lean_object* v_type_280_; lean_object* v_u_281_; lean_object* v_ringInst_282_; lean_object* v_semiringInst_283_; lean_object* v_charInst_x3f_284_; lean_object* v_addFn_x3f_285_; lean_object* v_mulFn_x3f_286_; lean_object* v_subFn_x3f_287_; lean_object* v_powFn_x3f_288_; lean_object* v_intCastFn_x3f_289_; lean_object* v_natCastFn_x3f_290_; lean_object* v_one_x3f_291_; lean_object* v_vars_292_; lean_object* v_varMap_293_; lean_object* v_denote_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_305_; 
v_id_279_ = lean_ctor_get(v_toRing_257_, 0);
v_type_280_ = lean_ctor_get(v_toRing_257_, 1);
v_u_281_ = lean_ctor_get(v_toRing_257_, 2);
v_ringInst_282_ = lean_ctor_get(v_toRing_257_, 3);
v_semiringInst_283_ = lean_ctor_get(v_toRing_257_, 4);
v_charInst_x3f_284_ = lean_ctor_get(v_toRing_257_, 5);
v_addFn_x3f_285_ = lean_ctor_get(v_toRing_257_, 6);
v_mulFn_x3f_286_ = lean_ctor_get(v_toRing_257_, 7);
v_subFn_x3f_287_ = lean_ctor_get(v_toRing_257_, 8);
v_powFn_x3f_288_ = lean_ctor_get(v_toRing_257_, 10);
v_intCastFn_x3f_289_ = lean_ctor_get(v_toRing_257_, 11);
v_natCastFn_x3f_290_ = lean_ctor_get(v_toRing_257_, 12);
v_one_x3f_291_ = lean_ctor_get(v_toRing_257_, 13);
v_vars_292_ = lean_ctor_get(v_toRing_257_, 14);
v_varMap_293_ = lean_ctor_get(v_toRing_257_, 15);
v_denote_294_ = lean_ctor_get(v_toRing_257_, 16);
v_isSharedCheck_305_ = !lean_is_exclusive(v_toRing_257_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_toRing_257_, 9);
lean_dec(v_unused_306_);
v___x_296_ = v_toRing_257_;
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_denote_294_);
lean_inc(v_varMap_293_);
lean_inc(v_vars_292_);
lean_inc(v_one_x3f_291_);
lean_inc(v_natCastFn_x3f_290_);
lean_inc(v_intCastFn_x3f_289_);
lean_inc(v_powFn_x3f_288_);
lean_inc(v_subFn_x3f_287_);
lean_inc(v_mulFn_x3f_286_);
lean_inc(v_addFn_x3f_285_);
lean_inc(v_charInst_x3f_284_);
lean_inc(v_semiringInst_283_);
lean_inc(v_ringInst_282_);
lean_inc(v_u_281_);
lean_inc(v_type_280_);
lean_inc(v_id_279_);
lean_dec(v_toRing_257_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_255_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 9, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_id_279_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_type_280_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_u_281_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_ringInst_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_semiringInst_283_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_charInst_x3f_284_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_addFn_x3f_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_mulFn_x3f_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_subFn_x3f_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 9, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_304_, 10, v_powFn_x3f_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 11, v_intCastFn_x3f_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 12, v_natCastFn_x3f_290_);
lean_ctor_set(v_reuseFailAlloc_304_, 13, v_one_x3f_291_);
lean_ctor_set(v_reuseFailAlloc_304_, 14, v_vars_292_);
lean_ctor_set(v_reuseFailAlloc_304_, 15, v_varMap_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 16, v_denote_294_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_300_);
v___x_302_ = v___x_277_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_invFn_x3f_258_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_semiringId_x3f_259_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_commSemiringInst_260_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_commRingInst_261_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_noZeroDivInst_x3f_262_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_fieldInst_x3f_263_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_powIdentityInst_x3f_264_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_denoteEntries_265_);
lean_ctor_set(v_reuseFailAlloc_303_, 9, v_nextId_266_);
lean_ctor_set(v_reuseFailAlloc_303_, 10, v_steps_267_);
lean_ctor_set(v_reuseFailAlloc_303_, 11, v_queue_268_);
lean_ctor_set(v_reuseFailAlloc_303_, 12, v_basis_269_);
lean_ctor_set(v_reuseFailAlloc_303_, 13, v_diseqs_270_);
lean_ctor_set(v_reuseFailAlloc_303_, 14, v_invSet_272_);
lean_ctor_set(v_reuseFailAlloc_303_, 15, v_powIdentityVarCount_273_);
lean_ctor_set(v_reuseFailAlloc_303_, 16, v_numEq0_x3f_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*17, v_recheck_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*17 + 1, v_numEq0Updated_275_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v_env_315_; lean_object* v___x_316_; lean_object* v_toCold_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_314_ = lean_st_ref_get(v___y_312_);
v_env_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_env_315_);
lean_dec(v___x_314_);
v___x_316_ = lean_st_ref_get(v___y_310_);
v_toCold_317_ = lean_ctor_get(v___y_311_, 0);
v_mctx_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_316_);
v_lctx_319_ = lean_ctor_get(v___y_309_, 2);
v_options_320_ = lean_ctor_get(v_toCold_317_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_315_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_308_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_ref_337_; lean_object* v___x_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_ref_337_ = lean_ctor_get(v___y_334_, 2);
v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_inc(v_ref_337_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_ref_337_);
lean_ctor_set(v___x_343_, 1, v_a_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 0, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
lean_inc_ref(v_type_358_);
v___x_371_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_358_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
if (lean_obj_tag(v_a_372_) == 1)
{
lean_object* v_val_376_; lean_object* v___x_378_; 
lean_dec_ref(v_type_358_);
v_val_376_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_372_, 1);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_val_376_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_val_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_del_object(v___x_374_);
lean_dec(v_a_372_);
v___x_380_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_381_ = l_Lean_indentExpr(v_type_358_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_382_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_383_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_type_358_);
v_a_385_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_371_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_371_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_407_, lean_object* v_u_408_, lean_object* v_instDeclName_409_, lean_object* v_declName_410_, lean_object* v_expectedInst_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v_u_408_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_inc_ref(v___x_425_);
v___x_426_ = l_Lean_mkConst(v_instDeclName_409_, v___x_425_);
lean_inc_ref(v_type_407_);
v___x_427_ = l_Lean_Expr_app___override(v___x_426_, v_type_407_);
v___x_428_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_427_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_429_, 2);
lean_dec_ref_known(v___x_428_, 1);
lean_inc(v_declName_410_);
v___x_430_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_410_, v_a_429_, v_expectedInst_411_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref_known(v___x_430_, 1);
v___x_431_ = l_Lean_mkConst(v_declName_410_, v___x_425_);
v___x_432_ = l_Lean_mkAppB(v___x_431_, v_type_407_, v_a_429_);
v___x_433_ = l_Lean_Meta_Sym_canon(v___x_432_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = l_Lean_Meta_Sym_shareCommon(v_a_434_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v___x_435_;
}
else
{
return v___x_433_;
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_429_);
lean_dec_ref_known(v___x_425_, 2);
lean_dec(v_declName_410_);
lean_dec_ref(v_type_407_);
v_a_436_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_430_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_430_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_425_, 2);
lean_dec_ref(v_expectedInst_411_);
lean_dec(v_declName_410_);
lean_dec_ref(v_type_407_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_444_ = _args[0];
lean_object* v_u_445_ = _args[1];
lean_object* v_instDeclName_446_ = _args[2];
lean_object* v_declName_447_ = _args[3];
lean_object* v_expectedInst_448_ = _args[4];
lean_object* v___y_449_ = _args[5];
lean_object* v___y_450_ = _args[6];
lean_object* v___y_451_ = _args[7];
lean_object* v___y_452_ = _args[8];
lean_object* v___y_453_ = _args[9];
lean_object* v___y_454_ = _args[10];
lean_object* v___y_455_ = _args[11];
lean_object* v___y_456_ = _args[12];
lean_object* v___y_457_ = _args[13];
lean_object* v___y_458_ = _args[14];
lean_object* v___y_459_ = _args[15];
lean_object* v___y_460_ = _args[16];
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_444_, v_u_445_, v_instDeclName_446_, v_declName_447_, v_expectedInst_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_531_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_531_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_531_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_531_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_toRing_495_; lean_object* v_negFn_x3f_496_; 
v_toRing_495_ = lean_ctor_get(v_a_491_, 0);
lean_inc_ref(v_toRing_495_);
lean_dec(v_a_491_);
v_negFn_x3f_496_ = lean_ctor_get(v_toRing_495_, 9);
if (lean_obj_tag(v_negFn_x3f_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; 
lean_inc_ref(v_negFn_x3f_496_);
lean_dec_ref(v_toRing_495_);
v_val_497_ = lean_ctor_get(v_negFn_x3f_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_negFn_x3f_496_, 1);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_val_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_val_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v_type_501_; lean_object* v_u_502_; lean_object* v_ringInst_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_expectedInst_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_del_object(v___x_493_);
v_type_501_ = lean_ctor_get(v_toRing_495_, 1);
lean_inc_ref_n(v_type_501_, 2);
v_u_502_ = lean_ctor_get(v_toRing_495_, 2);
lean_inc_n(v_u_502_, 2);
v_ringInst_503_ = lean_ctor_get(v_toRing_495_, 3);
lean_inc_ref(v_ringInst_503_);
lean_dec_ref(v_toRing_495_);
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v_u_502_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_mkConst(v___x_504_, v___x_506_);
v_expectedInst_508_ = l_Lean_mkAppB(v___x_507_, v_type_501_, v_ringInst_503_);
v___x_509_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_510_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8));
v___x_511_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_501_, v_u_502_, v___x_509_, v___x_510_, v_expectedInst_508_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___f_513_; lean_object* v___x_514_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc_n(v_a_512_, 2);
lean_dec_ref_known(v___x_511_, 1);
v___f_513_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_513_, 0, v_a_512_);
v___x_514_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_513_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v___x_514_, 0);
lean_dec(v_unused_522_);
v___x_516_ = v___x_514_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_dec(v___x_514_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v_a_512_);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_512_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_512_);
v_a_523_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_490_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_490_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_nat_to_int(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v_toRing_583_; lean_object* v_type_584_; lean_object* v_u_585_; lean_object* v_semiringInst_586_; lean_object* v___x_587_; lean_object* v_n_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v_toRing_583_ = lean_ctor_get(v_a_582_, 0);
lean_inc_ref(v_toRing_583_);
lean_dec(v_a_582_);
v_type_584_ = lean_ctor_get(v_toRing_583_, 1);
lean_inc_ref_n(v_type_584_, 2);
v_u_585_ = lean_ctor_get(v_toRing_583_, 2);
lean_inc(v_u_585_);
v_semiringInst_586_ = lean_ctor_get(v_toRing_583_, 4);
lean_inc_ref(v_semiringInst_586_);
lean_dec_ref(v_toRing_583_);
v___x_587_ = lean_nat_abs(v_k_568_);
v_n_588_ = l_Lean_mkRawNatLit(v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_u_585_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc_ref(v___x_591_);
v___x_592_ = l_Lean_mkConst(v___x_589_, v___x_591_);
lean_inc_ref(v_n_588_);
v___x_593_ = l_Lean_mkAppB(v___x_592_, v_type_584_, v_n_588_);
v___x_594_ = lean_box(0);
v___x_595_ = l_Lean_Meta_synthInstance_x3f(v___x_593_, v___x_594_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_635_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_635_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_ofNatInst_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; 
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_631_; 
lean_dec_ref(v_semiringInst_586_);
v_val_631_ = lean_ctor_get(v_a_596_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_a_596_, 1);
v_ofNatInst_601_ = v_val_631_;
v___y_602_ = v___y_569_;
v___y_603_ = v___y_570_;
v___y_604_ = v___y_571_;
v___y_605_ = v___y_572_;
v___y_606_ = v___y_573_;
v___y_607_ = v___y_574_;
v___y_608_ = v___y_575_;
v___y_609_ = v___y_576_;
v___y_610_ = v___y_577_;
v___y_611_ = v___y_578_;
v___y_612_ = v___y_579_;
goto v___jp_600_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_a_596_);
v___x_632_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6));
lean_inc_ref(v___x_591_);
v___x_633_ = l_Lean_mkConst(v___x_632_, v___x_591_);
lean_inc_ref(v_n_588_);
lean_inc_ref(v_type_584_);
v___x_634_ = l_Lean_mkApp3(v___x_633_, v_type_584_, v_semiringInst_586_, v_n_588_);
v_ofNatInst_601_ = v___x_634_;
v___y_602_ = v___y_569_;
v___y_603_ = v___y_570_;
v___y_604_ = v___y_571_;
v___y_605_ = v___y_572_;
v___y_606_ = v___y_573_;
v___y_607_ = v___y_574_;
v___y_608_ = v___y_575_;
v___y_609_ = v___y_576_;
v___y_610_ = v___y_577_;
v___y_611_ = v___y_578_;
v___y_612_ = v___y_579_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_n_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_613_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_614_ = l_Lean_mkConst(v___x_613_, v___x_591_);
v_n_615_ = l_Lean_mkApp3(v___x_614_, v_type_584_, v_n_588_, v_ofNatInst_601_);
v___x_616_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_617_ = lean_int_dec_lt(v_k_568_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_619_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_n_615_);
v___x_619_ = v___x_598_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_n_615_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v___x_621_; 
lean_del_object(v___x_598_);
v___x_621_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l_Lean_Expr_app___override(v_a_622_, v_n_615_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_dec_ref(v_n_615_);
return v___x_621_;
}
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref_known(v___x_591_, 2);
lean_dec_ref(v_n_588_);
lean_dec_ref(v_semiringInst_586_);
lean_dec_ref(v_type_584_);
v_a_636_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_595_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_595_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_581_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_581_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v_k_652_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_666_, lean_object* v_u_667_, lean_object* v_instDeclName_668_, lean_object* v_declName_669_, lean_object* v_expectedInst_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_683_ = lean_box(0);
lean_inc_n(v_u_667_, 2);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v_u_667_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v_u_667_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v_u_667_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
lean_inc_ref(v___x_686_);
v___x_687_ = l_Lean_mkConst(v_instDeclName_668_, v___x_686_);
lean_inc_ref_n(v_type_666_, 3);
v___x_688_ = l_Lean_mkApp3(v___x_687_, v_type_666_, v_type_666_, v_type_666_);
v___x_689_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_688_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_n(v_a_690_, 2);
lean_dec_ref_known(v___x_689_, 1);
lean_inc(v_declName_669_);
v___x_691_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_669_, v_a_690_, v_expectedInst_670_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref_known(v___x_691_, 1);
v___x_692_ = l_Lean_mkConst(v_declName_669_, v___x_686_);
lean_inc_ref_n(v_type_666_, 2);
v___x_693_ = l_Lean_mkApp4(v___x_692_, v_type_666_, v_type_666_, v_type_666_, v_a_690_);
v___x_694_ = l_Lean_Meta_Sym_canon(v___x_693_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Lean_Meta_Sym_shareCommon(v_a_695_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_696_;
}
else
{
return v___x_694_;
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_a_690_);
lean_dec_ref_known(v___x_686_, 2);
lean_dec(v_declName_669_);
lean_dec_ref(v_type_666_);
v_a_697_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_691_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_686_, 2);
lean_dec_ref(v_expectedInst_670_);
lean_dec(v_declName_669_);
lean_dec_ref(v_type_666_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_705_ = _args[0];
lean_object* v_u_706_ = _args[1];
lean_object* v_instDeclName_707_ = _args[2];
lean_object* v_declName_708_ = _args[3];
lean_object* v_expectedInst_709_ = _args[4];
lean_object* v___y_710_ = _args[5];
lean_object* v___y_711_ = _args[6];
lean_object* v___y_712_ = _args[7];
lean_object* v___y_713_ = _args[8];
lean_object* v___y_714_ = _args[9];
lean_object* v___y_715_ = _args[10];
lean_object* v___y_716_ = _args[11];
lean_object* v___y_717_ = _args[12];
lean_object* v___y_718_ = _args[13];
lean_object* v___y_719_ = _args[14];
lean_object* v___y_720_ = _args[15];
lean_object* v___y_721_ = _args[16];
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_705_, v_u_706_, v_instDeclName_707_, v_declName_708_, v_expectedInst_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_723_, lean_object* v_s_724_){
_start:
{
lean_object* v_toRing_725_; lean_object* v_invFn_x3f_726_; lean_object* v_semiringId_x3f_727_; lean_object* v_commSemiringInst_728_; lean_object* v_commRingInst_729_; lean_object* v_noZeroDivInst_x3f_730_; lean_object* v_fieldInst_x3f_731_; lean_object* v_powIdentityInst_x3f_732_; lean_object* v_denoteEntries_733_; lean_object* v_nextId_734_; lean_object* v_steps_735_; lean_object* v_queue_736_; lean_object* v_basis_737_; lean_object* v_diseqs_738_; uint8_t v_recheck_739_; lean_object* v_invSet_740_; lean_object* v_powIdentityVarCount_741_; lean_object* v_numEq0_x3f_742_; uint8_t v_numEq0Updated_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_775_; 
v_toRing_725_ = lean_ctor_get(v_s_724_, 0);
v_invFn_x3f_726_ = lean_ctor_get(v_s_724_, 1);
v_semiringId_x3f_727_ = lean_ctor_get(v_s_724_, 2);
v_commSemiringInst_728_ = lean_ctor_get(v_s_724_, 3);
v_commRingInst_729_ = lean_ctor_get(v_s_724_, 4);
v_noZeroDivInst_x3f_730_ = lean_ctor_get(v_s_724_, 5);
v_fieldInst_x3f_731_ = lean_ctor_get(v_s_724_, 6);
v_powIdentityInst_x3f_732_ = lean_ctor_get(v_s_724_, 7);
v_denoteEntries_733_ = lean_ctor_get(v_s_724_, 8);
v_nextId_734_ = lean_ctor_get(v_s_724_, 9);
v_steps_735_ = lean_ctor_get(v_s_724_, 10);
v_queue_736_ = lean_ctor_get(v_s_724_, 11);
v_basis_737_ = lean_ctor_get(v_s_724_, 12);
v_diseqs_738_ = lean_ctor_get(v_s_724_, 13);
v_recheck_739_ = lean_ctor_get_uint8(v_s_724_, sizeof(void*)*17);
v_invSet_740_ = lean_ctor_get(v_s_724_, 14);
v_powIdentityVarCount_741_ = lean_ctor_get(v_s_724_, 15);
v_numEq0_x3f_742_ = lean_ctor_get(v_s_724_, 16);
v_numEq0Updated_743_ = lean_ctor_get_uint8(v_s_724_, sizeof(void*)*17 + 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_s_724_);
if (v_isSharedCheck_775_ == 0)
{
v___x_745_ = v_s_724_;
v_isShared_746_ = v_isSharedCheck_775_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_numEq0_x3f_742_);
lean_inc(v_powIdentityVarCount_741_);
lean_inc(v_invSet_740_);
lean_inc(v_diseqs_738_);
lean_inc(v_basis_737_);
lean_inc(v_queue_736_);
lean_inc(v_steps_735_);
lean_inc(v_nextId_734_);
lean_inc(v_denoteEntries_733_);
lean_inc(v_powIdentityInst_x3f_732_);
lean_inc(v_fieldInst_x3f_731_);
lean_inc(v_noZeroDivInst_x3f_730_);
lean_inc(v_commRingInst_729_);
lean_inc(v_commSemiringInst_728_);
lean_inc(v_semiringId_x3f_727_);
lean_inc(v_invFn_x3f_726_);
lean_inc(v_toRing_725_);
lean_dec(v_s_724_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_775_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_id_747_; lean_object* v_type_748_; lean_object* v_u_749_; lean_object* v_ringInst_750_; lean_object* v_semiringInst_751_; lean_object* v_charInst_x3f_752_; lean_object* v_addFn_x3f_753_; lean_object* v_subFn_x3f_754_; lean_object* v_negFn_x3f_755_; lean_object* v_powFn_x3f_756_; lean_object* v_intCastFn_x3f_757_; lean_object* v_natCastFn_x3f_758_; lean_object* v_one_x3f_759_; lean_object* v_vars_760_; lean_object* v_varMap_761_; lean_object* v_denote_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
v_id_747_ = lean_ctor_get(v_toRing_725_, 0);
v_type_748_ = lean_ctor_get(v_toRing_725_, 1);
v_u_749_ = lean_ctor_get(v_toRing_725_, 2);
v_ringInst_750_ = lean_ctor_get(v_toRing_725_, 3);
v_semiringInst_751_ = lean_ctor_get(v_toRing_725_, 4);
v_charInst_x3f_752_ = lean_ctor_get(v_toRing_725_, 5);
v_addFn_x3f_753_ = lean_ctor_get(v_toRing_725_, 6);
v_subFn_x3f_754_ = lean_ctor_get(v_toRing_725_, 8);
v_negFn_x3f_755_ = lean_ctor_get(v_toRing_725_, 9);
v_powFn_x3f_756_ = lean_ctor_get(v_toRing_725_, 10);
v_intCastFn_x3f_757_ = lean_ctor_get(v_toRing_725_, 11);
v_natCastFn_x3f_758_ = lean_ctor_get(v_toRing_725_, 12);
v_one_x3f_759_ = lean_ctor_get(v_toRing_725_, 13);
v_vars_760_ = lean_ctor_get(v_toRing_725_, 14);
v_varMap_761_ = lean_ctor_get(v_toRing_725_, 15);
v_denote_762_ = lean_ctor_get(v_toRing_725_, 16);
v_isSharedCheck_773_ = !lean_is_exclusive(v_toRing_725_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_toRing_725_, 7);
lean_dec(v_unused_774_);
v___x_764_ = v_toRing_725_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_denote_762_);
lean_inc(v_varMap_761_);
lean_inc(v_vars_760_);
lean_inc(v_one_x3f_759_);
lean_inc(v_natCastFn_x3f_758_);
lean_inc(v_intCastFn_x3f_757_);
lean_inc(v_powFn_x3f_756_);
lean_inc(v_negFn_x3f_755_);
lean_inc(v_subFn_x3f_754_);
lean_inc(v_addFn_x3f_753_);
lean_inc(v_charInst_x3f_752_);
lean_inc(v_semiringInst_751_);
lean_inc(v_ringInst_750_);
lean_inc(v_u_749_);
lean_inc(v_type_748_);
lean_inc(v_id_747_);
lean_dec(v_toRing_725_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_723_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 7, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_id_747_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_type_748_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_u_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_ringInst_750_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_semiringInst_751_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_charInst_x3f_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_addFn_x3f_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_subFn_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 9, v_negFn_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 10, v_powFn_x3f_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 11, v_intCastFn_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 12, v_natCastFn_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 13, v_one_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_772_, 14, v_vars_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 15, v_varMap_761_);
lean_ctor_set(v_reuseFailAlloc_772_, 16, v_denote_762_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_768_);
v___x_770_ = v___x_745_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_invFn_x3f_726_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_semiringId_x3f_727_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_commSemiringInst_728_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_commRingInst_729_);
lean_ctor_set(v_reuseFailAlloc_771_, 5, v_noZeroDivInst_x3f_730_);
lean_ctor_set(v_reuseFailAlloc_771_, 6, v_fieldInst_x3f_731_);
lean_ctor_set(v_reuseFailAlloc_771_, 7, v_powIdentityInst_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_771_, 8, v_denoteEntries_733_);
lean_ctor_set(v_reuseFailAlloc_771_, 9, v_nextId_734_);
lean_ctor_set(v_reuseFailAlloc_771_, 10, v_steps_735_);
lean_ctor_set(v_reuseFailAlloc_771_, 11, v_queue_736_);
lean_ctor_set(v_reuseFailAlloc_771_, 12, v_basis_737_);
lean_ctor_set(v_reuseFailAlloc_771_, 13, v_diseqs_738_);
lean_ctor_set(v_reuseFailAlloc_771_, 14, v_invSet_740_);
lean_ctor_set(v_reuseFailAlloc_771_, 15, v_powIdentityVarCount_741_);
lean_ctor_set(v_reuseFailAlloc_771_, 16, v_numEq0_x3f_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*17, v_recheck_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*17 + 1, v_numEq0Updated_743_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_843_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_843_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_843_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_843_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_toRing_804_; lean_object* v_mulFn_x3f_805_; 
v_toRing_804_ = lean_ctor_get(v_a_800_, 0);
lean_inc_ref(v_toRing_804_);
lean_dec(v_a_800_);
v_mulFn_x3f_805_ = lean_ctor_get(v_toRing_804_, 7);
if (lean_obj_tag(v_mulFn_x3f_805_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_808_; 
lean_inc_ref(v_mulFn_x3f_805_);
lean_dec_ref(v_toRing_804_);
v_val_806_ = lean_ctor_get(v_mulFn_x3f_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_mulFn_x3f_805_, 1);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_val_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v_type_810_; lean_object* v_u_811_; lean_object* v_semiringInst_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_expectedInst_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_802_);
v_type_810_ = lean_ctor_get(v_toRing_804_, 1);
lean_inc_ref_n(v_type_810_, 3);
v_u_811_ = lean_ctor_get(v_toRing_804_, 2);
lean_inc_n(v_u_811_, 2);
v_semiringInst_812_ = lean_ctor_get(v_toRing_804_, 4);
lean_inc_ref(v_semiringInst_812_);
lean_dec_ref(v_toRing_804_);
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v_u_811_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
lean_inc_ref(v___x_815_);
v___x_816_ = l_Lean_mkConst(v___x_813_, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_818_ = l_Lean_mkConst(v___x_817_, v___x_815_);
v___x_819_ = l_Lean_mkAppB(v___x_818_, v_type_810_, v_semiringInst_812_);
v_expectedInst_820_ = l_Lean_mkAppB(v___x_816_, v_type_810_, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_822_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_823_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_810_, v_u_811_, v___x_821_, v___x_822_, v_expectedInst_820_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_n(v_a_824_, 2);
lean_dec_ref_known(v___x_823_, 1);
v___f_825_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_825_, 0, v_a_824_);
v___x_826_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_825_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_826_, 0);
lean_dec(v_unused_834_);
v___x_828_ = v___x_826_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v___x_826_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_a_824_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_824_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_824_);
v_a_835_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_826_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_826_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_799_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_799_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_865_, lean_object* v_s_866_){
_start:
{
lean_object* v_toRing_867_; lean_object* v_invFn_x3f_868_; lean_object* v_semiringId_x3f_869_; lean_object* v_commSemiringInst_870_; lean_object* v_commRingInst_871_; lean_object* v_noZeroDivInst_x3f_872_; lean_object* v_fieldInst_x3f_873_; lean_object* v_powIdentityInst_x3f_874_; lean_object* v_denoteEntries_875_; lean_object* v_nextId_876_; lean_object* v_steps_877_; lean_object* v_queue_878_; lean_object* v_basis_879_; lean_object* v_diseqs_880_; uint8_t v_recheck_881_; lean_object* v_invSet_882_; lean_object* v_powIdentityVarCount_883_; lean_object* v_numEq0_x3f_884_; uint8_t v_numEq0Updated_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_917_; 
v_toRing_867_ = lean_ctor_get(v_s_866_, 0);
v_invFn_x3f_868_ = lean_ctor_get(v_s_866_, 1);
v_semiringId_x3f_869_ = lean_ctor_get(v_s_866_, 2);
v_commSemiringInst_870_ = lean_ctor_get(v_s_866_, 3);
v_commRingInst_871_ = lean_ctor_get(v_s_866_, 4);
v_noZeroDivInst_x3f_872_ = lean_ctor_get(v_s_866_, 5);
v_fieldInst_x3f_873_ = lean_ctor_get(v_s_866_, 6);
v_powIdentityInst_x3f_874_ = lean_ctor_get(v_s_866_, 7);
v_denoteEntries_875_ = lean_ctor_get(v_s_866_, 8);
v_nextId_876_ = lean_ctor_get(v_s_866_, 9);
v_steps_877_ = lean_ctor_get(v_s_866_, 10);
v_queue_878_ = lean_ctor_get(v_s_866_, 11);
v_basis_879_ = lean_ctor_get(v_s_866_, 12);
v_diseqs_880_ = lean_ctor_get(v_s_866_, 13);
v_recheck_881_ = lean_ctor_get_uint8(v_s_866_, sizeof(void*)*17);
v_invSet_882_ = lean_ctor_get(v_s_866_, 14);
v_powIdentityVarCount_883_ = lean_ctor_get(v_s_866_, 15);
v_numEq0_x3f_884_ = lean_ctor_get(v_s_866_, 16);
v_numEq0Updated_885_ = lean_ctor_get_uint8(v_s_866_, sizeof(void*)*17 + 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_s_866_);
if (v_isSharedCheck_917_ == 0)
{
v___x_887_ = v_s_866_;
v_isShared_888_ = v_isSharedCheck_917_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_numEq0_x3f_884_);
lean_inc(v_powIdentityVarCount_883_);
lean_inc(v_invSet_882_);
lean_inc(v_diseqs_880_);
lean_inc(v_basis_879_);
lean_inc(v_queue_878_);
lean_inc(v_steps_877_);
lean_inc(v_nextId_876_);
lean_inc(v_denoteEntries_875_);
lean_inc(v_powIdentityInst_x3f_874_);
lean_inc(v_fieldInst_x3f_873_);
lean_inc(v_noZeroDivInst_x3f_872_);
lean_inc(v_commRingInst_871_);
lean_inc(v_commSemiringInst_870_);
lean_inc(v_semiringId_x3f_869_);
lean_inc(v_invFn_x3f_868_);
lean_inc(v_toRing_867_);
lean_dec(v_s_866_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_917_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_id_889_; lean_object* v_type_890_; lean_object* v_u_891_; lean_object* v_ringInst_892_; lean_object* v_semiringInst_893_; lean_object* v_charInst_x3f_894_; lean_object* v_addFn_x3f_895_; lean_object* v_mulFn_x3f_896_; lean_object* v_subFn_x3f_897_; lean_object* v_negFn_x3f_898_; lean_object* v_intCastFn_x3f_899_; lean_object* v_natCastFn_x3f_900_; lean_object* v_one_x3f_901_; lean_object* v_vars_902_; lean_object* v_varMap_903_; lean_object* v_denote_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_915_; 
v_id_889_ = lean_ctor_get(v_toRing_867_, 0);
v_type_890_ = lean_ctor_get(v_toRing_867_, 1);
v_u_891_ = lean_ctor_get(v_toRing_867_, 2);
v_ringInst_892_ = lean_ctor_get(v_toRing_867_, 3);
v_semiringInst_893_ = lean_ctor_get(v_toRing_867_, 4);
v_charInst_x3f_894_ = lean_ctor_get(v_toRing_867_, 5);
v_addFn_x3f_895_ = lean_ctor_get(v_toRing_867_, 6);
v_mulFn_x3f_896_ = lean_ctor_get(v_toRing_867_, 7);
v_subFn_x3f_897_ = lean_ctor_get(v_toRing_867_, 8);
v_negFn_x3f_898_ = lean_ctor_get(v_toRing_867_, 9);
v_intCastFn_x3f_899_ = lean_ctor_get(v_toRing_867_, 11);
v_natCastFn_x3f_900_ = lean_ctor_get(v_toRing_867_, 12);
v_one_x3f_901_ = lean_ctor_get(v_toRing_867_, 13);
v_vars_902_ = lean_ctor_get(v_toRing_867_, 14);
v_varMap_903_ = lean_ctor_get(v_toRing_867_, 15);
v_denote_904_ = lean_ctor_get(v_toRing_867_, 16);
v_isSharedCheck_915_ = !lean_is_exclusive(v_toRing_867_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_toRing_867_, 10);
lean_dec(v_unused_916_);
v___x_906_ = v_toRing_867_;
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_denote_904_);
lean_inc(v_varMap_903_);
lean_inc(v_vars_902_);
lean_inc(v_one_x3f_901_);
lean_inc(v_natCastFn_x3f_900_);
lean_inc(v_intCastFn_x3f_899_);
lean_inc(v_negFn_x3f_898_);
lean_inc(v_subFn_x3f_897_);
lean_inc(v_mulFn_x3f_896_);
lean_inc(v_addFn_x3f_895_);
lean_inc(v_charInst_x3f_894_);
lean_inc(v_semiringInst_893_);
lean_inc(v_ringInst_892_);
lean_inc(v_u_891_);
lean_inc(v_type_890_);
lean_inc(v_id_889_);
lean_dec(v_toRing_867_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_a_865_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 10, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_id_889_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_type_890_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_u_891_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_ringInst_892_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_semiringInst_893_);
lean_ctor_set(v_reuseFailAlloc_914_, 5, v_charInst_x3f_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 6, v_addFn_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_914_, 7, v_mulFn_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_914_, 8, v_subFn_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_914_, 9, v_negFn_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_914_, 10, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 11, v_intCastFn_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_914_, 12, v_natCastFn_x3f_900_);
lean_ctor_set(v_reuseFailAlloc_914_, 13, v_one_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_914_, 14, v_vars_902_);
lean_ctor_set(v_reuseFailAlloc_914_, 15, v_varMap_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 16, v_denote_904_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_910_);
v___x_912_ = v___x_887_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_invFn_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_semiringId_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_commSemiringInst_870_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_commRingInst_871_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_noZeroDivInst_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_fieldInst_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_powIdentityInst_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_denoteEntries_875_);
lean_ctor_set(v_reuseFailAlloc_913_, 9, v_nextId_876_);
lean_ctor_set(v_reuseFailAlloc_913_, 10, v_steps_877_);
lean_ctor_set(v_reuseFailAlloc_913_, 11, v_queue_878_);
lean_ctor_set(v_reuseFailAlloc_913_, 12, v_basis_879_);
lean_ctor_set(v_reuseFailAlloc_913_, 13, v_diseqs_880_);
lean_ctor_set(v_reuseFailAlloc_913_, 14, v_invSet_882_);
lean_ctor_set(v_reuseFailAlloc_913_, 15, v_powIdentityVarCount_883_);
lean_ctor_set(v_reuseFailAlloc_913_, 16, v_numEq0_x3f_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*17, v_recheck_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*17 + 1, v_numEq0Updated_885_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Lean_Level_ofNat(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_928_, lean_object* v_type_929_, lean_object* v_semiringInst_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_943_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_944_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_945_ = lean_box(0);
lean_inc(v_u_928_);
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v_u_928_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
lean_inc_ref(v___x_946_);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_944_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v_u_928_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
lean_inc_ref(v___x_948_);
v___x_949_ = l_Lean_mkConst(v___x_943_, v___x_948_);
v___x_950_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_929_, 2);
v___x_951_ = l_Lean_mkApp3(v___x_949_, v_type_929_, v___x_950_, v_type_929_);
v___x_952_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_951_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_inst_x27_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc_n(v_a_953_, 2);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_955_ = l_Lean_mkConst(v___x_954_, v___x_946_);
lean_inc_ref(v_type_929_);
v_inst_x27_956_ = l_Lean_mkAppB(v___x_955_, v_type_929_, v_semiringInst_930_);
v___x_957_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_958_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_957_, v_a_953_, v_inst_x27_956_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref_known(v___x_958_, 1);
v___x_959_ = l_Lean_mkConst(v___x_957_, v___x_948_);
lean_inc_ref(v_type_929_);
v___x_960_ = l_Lean_mkApp4(v___x_959_, v_type_929_, v___x_950_, v_type_929_, v_a_953_);
v___x_961_ = l_Lean_Meta_Sym_canon(v___x_960_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = l_Lean_Meta_Sym_shareCommon(v_a_962_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_963_;
}
else
{
return v___x_961_;
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_a_953_);
lean_dec_ref_known(v___x_948_, 2);
lean_dec_ref(v_type_929_);
v_a_964_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_958_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_958_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_948_, 2);
lean_dec_ref_known(v___x_946_, 2);
lean_dec_ref(v_semiringInst_930_);
lean_dec_ref(v_type_929_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_972_, lean_object* v_type_973_, lean_object* v_semiringInst_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_972_, v_type_973_, v_semiringInst_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1034_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1034_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1034_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_toRing_1005_; lean_object* v_powFn_x3f_1006_; 
v_toRing_1005_ = lean_ctor_get(v_a_1001_, 0);
lean_inc_ref(v_toRing_1005_);
lean_dec(v_a_1001_);
v_powFn_x3f_1006_ = lean_ctor_get(v_toRing_1005_, 10);
if (lean_obj_tag(v_powFn_x3f_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
lean_inc_ref(v_powFn_x3f_1006_);
lean_dec_ref(v_toRing_1005_);
v_val_1007_ = lean_ctor_get(v_powFn_x3f_1006_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_powFn_x3f_1006_, 1);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_val_1007_);
v___x_1009_ = v___x_1003_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v_type_1011_; lean_object* v_u_1012_; lean_object* v_semiringInst_1013_; lean_object* v___x_1014_; 
lean_del_object(v___x_1003_);
v_type_1011_ = lean_ctor_get(v_toRing_1005_, 1);
lean_inc_ref(v_type_1011_);
v_u_1012_ = lean_ctor_get(v_toRing_1005_, 2);
lean_inc(v_u_1012_);
v_semiringInst_1013_ = lean_ctor_get(v_toRing_1005_, 4);
lean_inc_ref(v_semiringInst_1013_);
lean_dec_ref(v_toRing_1005_);
v___x_1014_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1012_, v_type_1011_, v_semiringInst_1013_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_n(v_a_1015_, 2);
lean_dec_ref_known(v___x_1014_, 1);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1016_, 0, v_a_1015_);
v___x_1017_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1016_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1025_);
v___x_1019_ = v___x_1017_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v___x_1017_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v_a_1015_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1015_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1015_);
v_a_1026_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1000_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1000_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1101_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1101_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1101_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_toRing_1074_; lean_object* v_vars_1075_; lean_object* v_x_1076_; lean_object* v_k_1077_; lean_object* v___y_1079_; lean_object* v_size_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_toRing_1074_ = lean_ctor_get(v_a_1070_, 0);
lean_inc_ref(v_toRing_1074_);
lean_dec(v_a_1070_);
v_vars_1075_ = lean_ctor_get(v_toRing_1074_, 14);
lean_inc_ref(v_vars_1075_);
lean_dec_ref(v_toRing_1074_);
v_x_1076_ = lean_ctor_get(v_pw_1056_, 0);
lean_inc(v_x_1076_);
v_k_1077_ = lean_ctor_get(v_pw_1056_, 1);
lean_inc(v_k_1077_);
lean_dec_ref(v_pw_1056_);
v_size_1096_ = lean_ctor_get(v_vars_1075_, 2);
v___x_1097_ = l_Lean_instInhabitedExpr;
v___x_1098_ = lean_nat_dec_lt(v_x_1076_, v_size_1096_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_x_1076_);
lean_dec_ref(v_vars_1075_);
v___x_1099_ = l_outOfBounds___redArg(v___x_1097_);
v___y_1079_ = v___x_1099_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1097_, v_vars_1075_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec_ref(v_vars_1075_);
v___y_1079_ = v___x_1100_;
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_dec_eq(v_k_1077_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_del_object(v___x_1072_);
v___x_1082_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1092_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = l_Lean_mkNatLit(v_k_1077_);
v___x_1088_ = l_Lean_mkAppB(v_a_1083_, v___y_1079_, v___x_1087_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_dec_ref(v___y_1079_);
lean_dec(v_k_1077_);
return v___x_1082_;
}
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_k_1077_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___y_1079_);
v___x_1094_ = v___x_1072_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___y_1079_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v_pw_1056_);
v_a_1102_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1069_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1069_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_m_1124_, lean_object* v_acc_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
if (lean_obj_tag(v_m_1124_) == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_acc_1125_);
return v___x_1138_;
}
else
{
lean_object* v_p_1139_; lean_object* v_m_1140_; lean_object* v___x_1141_; 
v_p_1139_ = lean_ctor_get(v_m_1124_, 0);
lean_inc_ref(v_p_1139_);
v_m_1140_ = lean_ctor_get(v_m_1124_, 1);
lean_inc(v_m_1140_);
lean_dec_ref_known(v_m_1124_, 2);
v___x_1141_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1139_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = l_Lean_mkAppB(v_a_1142_, v_acc_1125_, v_a_1144_);
v_m_1124_ = v_m_1140_;
v_acc_1125_ = v___x_1145_;
goto _start;
}
else
{
lean_dec(v_a_1142_);
lean_dec(v_m_1140_);
lean_dec_ref(v_acc_1125_);
return v___x_1143_;
}
}
else
{
lean_dec(v_m_1140_);
lean_dec_ref(v_p_1139_);
lean_dec_ref(v_acc_1125_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_m_1147_, lean_object* v_acc_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1147_, v_acc_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_to_int(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_m_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
if (lean_obj_tag(v_m_1164_) == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1178_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1177_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1178_;
}
else
{
lean_object* v_p_1179_; lean_object* v_m_1180_; lean_object* v___x_1181_; 
v_p_1179_ = lean_ctor_get(v_m_1164_, 0);
lean_inc_ref(v_p_1179_);
v_m_1180_ = lean_ctor_get(v_m_1164_, 1);
lean_inc(v_m_1180_);
lean_dec_ref_known(v_m_1164_, 2);
v___x_1181_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1179_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1180_, v_a_1182_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1183_;
}
else
{
lean_dec(v_m_1180_);
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_m_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1198_, lean_object* v_m_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1213_ = lean_int_dec_eq(v_k_1198_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_mkAppB(v_a_1215_, v_a_1217_, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_dec(v_a_1217_);
lean_dec(v_a_1215_);
return v___x_1218_;
}
}
else
{
lean_dec(v_a_1215_);
lean_dec(v_m_1199_);
return v___x_1216_;
}
}
else
{
lean_dec(v_m_1199_);
return v___x_1214_;
}
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1229_, lean_object* v_m_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1229_, v_m_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v_k_1229_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_1244_, lean_object* v_s_1245_){
_start:
{
lean_object* v_toRing_1246_; lean_object* v_invFn_x3f_1247_; lean_object* v_semiringId_x3f_1248_; lean_object* v_commSemiringInst_1249_; lean_object* v_commRingInst_1250_; lean_object* v_noZeroDivInst_x3f_1251_; lean_object* v_fieldInst_x3f_1252_; lean_object* v_powIdentityInst_x3f_1253_; lean_object* v_denoteEntries_1254_; lean_object* v_nextId_1255_; lean_object* v_steps_1256_; lean_object* v_queue_1257_; lean_object* v_basis_1258_; lean_object* v_diseqs_1259_; uint8_t v_recheck_1260_; lean_object* v_invSet_1261_; lean_object* v_powIdentityVarCount_1262_; lean_object* v_numEq0_x3f_1263_; uint8_t v_numEq0Updated_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1296_; 
v_toRing_1246_ = lean_ctor_get(v_s_1245_, 0);
v_invFn_x3f_1247_ = lean_ctor_get(v_s_1245_, 1);
v_semiringId_x3f_1248_ = lean_ctor_get(v_s_1245_, 2);
v_commSemiringInst_1249_ = lean_ctor_get(v_s_1245_, 3);
v_commRingInst_1250_ = lean_ctor_get(v_s_1245_, 4);
v_noZeroDivInst_x3f_1251_ = lean_ctor_get(v_s_1245_, 5);
v_fieldInst_x3f_1252_ = lean_ctor_get(v_s_1245_, 6);
v_powIdentityInst_x3f_1253_ = lean_ctor_get(v_s_1245_, 7);
v_denoteEntries_1254_ = lean_ctor_get(v_s_1245_, 8);
v_nextId_1255_ = lean_ctor_get(v_s_1245_, 9);
v_steps_1256_ = lean_ctor_get(v_s_1245_, 10);
v_queue_1257_ = lean_ctor_get(v_s_1245_, 11);
v_basis_1258_ = lean_ctor_get(v_s_1245_, 12);
v_diseqs_1259_ = lean_ctor_get(v_s_1245_, 13);
v_recheck_1260_ = lean_ctor_get_uint8(v_s_1245_, sizeof(void*)*17);
v_invSet_1261_ = lean_ctor_get(v_s_1245_, 14);
v_powIdentityVarCount_1262_ = lean_ctor_get(v_s_1245_, 15);
v_numEq0_x3f_1263_ = lean_ctor_get(v_s_1245_, 16);
v_numEq0Updated_1264_ = lean_ctor_get_uint8(v_s_1245_, sizeof(void*)*17 + 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_s_1245_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1266_ = v_s_1245_;
v_isShared_1267_ = v_isSharedCheck_1296_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_numEq0_x3f_1263_);
lean_inc(v_powIdentityVarCount_1262_);
lean_inc(v_invSet_1261_);
lean_inc(v_diseqs_1259_);
lean_inc(v_basis_1258_);
lean_inc(v_queue_1257_);
lean_inc(v_steps_1256_);
lean_inc(v_nextId_1255_);
lean_inc(v_denoteEntries_1254_);
lean_inc(v_powIdentityInst_x3f_1253_);
lean_inc(v_fieldInst_x3f_1252_);
lean_inc(v_noZeroDivInst_x3f_1251_);
lean_inc(v_commRingInst_1250_);
lean_inc(v_commSemiringInst_1249_);
lean_inc(v_semiringId_x3f_1248_);
lean_inc(v_invFn_x3f_1247_);
lean_inc(v_toRing_1246_);
lean_dec(v_s_1245_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1296_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_id_1268_; lean_object* v_type_1269_; lean_object* v_u_1270_; lean_object* v_ringInst_1271_; lean_object* v_semiringInst_1272_; lean_object* v_charInst_x3f_1273_; lean_object* v_mulFn_x3f_1274_; lean_object* v_subFn_x3f_1275_; lean_object* v_negFn_x3f_1276_; lean_object* v_powFn_x3f_1277_; lean_object* v_intCastFn_x3f_1278_; lean_object* v_natCastFn_x3f_1279_; lean_object* v_one_x3f_1280_; lean_object* v_vars_1281_; lean_object* v_varMap_1282_; lean_object* v_denote_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1294_; 
v_id_1268_ = lean_ctor_get(v_toRing_1246_, 0);
v_type_1269_ = lean_ctor_get(v_toRing_1246_, 1);
v_u_1270_ = lean_ctor_get(v_toRing_1246_, 2);
v_ringInst_1271_ = lean_ctor_get(v_toRing_1246_, 3);
v_semiringInst_1272_ = lean_ctor_get(v_toRing_1246_, 4);
v_charInst_x3f_1273_ = lean_ctor_get(v_toRing_1246_, 5);
v_mulFn_x3f_1274_ = lean_ctor_get(v_toRing_1246_, 7);
v_subFn_x3f_1275_ = lean_ctor_get(v_toRing_1246_, 8);
v_negFn_x3f_1276_ = lean_ctor_get(v_toRing_1246_, 9);
v_powFn_x3f_1277_ = lean_ctor_get(v_toRing_1246_, 10);
v_intCastFn_x3f_1278_ = lean_ctor_get(v_toRing_1246_, 11);
v_natCastFn_x3f_1279_ = lean_ctor_get(v_toRing_1246_, 12);
v_one_x3f_1280_ = lean_ctor_get(v_toRing_1246_, 13);
v_vars_1281_ = lean_ctor_get(v_toRing_1246_, 14);
v_varMap_1282_ = lean_ctor_get(v_toRing_1246_, 15);
v_denote_1283_ = lean_ctor_get(v_toRing_1246_, 16);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_toRing_1246_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_toRing_1246_, 6);
lean_dec(v_unused_1295_);
v___x_1285_ = v_toRing_1246_;
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_denote_1283_);
lean_inc(v_varMap_1282_);
lean_inc(v_vars_1281_);
lean_inc(v_one_x3f_1280_);
lean_inc(v_natCastFn_x3f_1279_);
lean_inc(v_intCastFn_x3f_1278_);
lean_inc(v_powFn_x3f_1277_);
lean_inc(v_negFn_x3f_1276_);
lean_inc(v_subFn_x3f_1275_);
lean_inc(v_mulFn_x3f_1274_);
lean_inc(v_charInst_x3f_1273_);
lean_inc(v_semiringInst_1272_);
lean_inc(v_ringInst_1271_);
lean_inc(v_u_1270_);
lean_inc(v_type_1269_);
lean_inc(v_id_1268_);
lean_dec(v_toRing_1246_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_a_1244_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 6, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_id_1268_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_type_1269_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_u_1270_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_ringInst_1271_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_semiringInst_1272_);
lean_ctor_set(v_reuseFailAlloc_1293_, 5, v_charInst_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1293_, 6, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 7, v_mulFn_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1293_, 8, v_subFn_x3f_1275_);
lean_ctor_set(v_reuseFailAlloc_1293_, 9, v_negFn_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 10, v_powFn_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 11, v_intCastFn_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 12, v_natCastFn_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1293_, 13, v_one_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 14, v_vars_1281_);
lean_ctor_set(v_reuseFailAlloc_1293_, 15, v_varMap_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 16, v_denote_1283_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1289_);
v___x_1291_ = v___x_1266_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_invFn_x3f_1247_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_semiringId_x3f_1248_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_commSemiringInst_1249_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_commRingInst_1250_);
lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_noZeroDivInst_x3f_1251_);
lean_ctor_set(v_reuseFailAlloc_1292_, 6, v_fieldInst_x3f_1252_);
lean_ctor_set(v_reuseFailAlloc_1292_, 7, v_powIdentityInst_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1292_, 8, v_denoteEntries_1254_);
lean_ctor_set(v_reuseFailAlloc_1292_, 9, v_nextId_1255_);
lean_ctor_set(v_reuseFailAlloc_1292_, 10, v_steps_1256_);
lean_ctor_set(v_reuseFailAlloc_1292_, 11, v_queue_1257_);
lean_ctor_set(v_reuseFailAlloc_1292_, 12, v_basis_1258_);
lean_ctor_set(v_reuseFailAlloc_1292_, 13, v_diseqs_1259_);
lean_ctor_set(v_reuseFailAlloc_1292_, 14, v_invSet_1261_);
lean_ctor_set(v_reuseFailAlloc_1292_, 15, v_powIdentityVarCount_1262_);
lean_ctor_set(v_reuseFailAlloc_1292_, 16, v_numEq0_x3f_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*17, v_recheck_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*17 + 1, v_numEq0Updated_1264_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1369_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1369_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1369_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_toRing_1330_; lean_object* v_addFn_x3f_1331_; 
v_toRing_1330_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_toRing_1330_);
lean_dec(v_a_1326_);
v_addFn_x3f_1331_ = lean_ctor_get(v_toRing_1330_, 6);
if (lean_obj_tag(v_addFn_x3f_1331_) == 1)
{
lean_object* v_val_1332_; lean_object* v___x_1334_; 
lean_inc_ref(v_addFn_x3f_1331_);
lean_dec_ref(v_toRing_1330_);
v_val_1332_ = lean_ctor_get(v_addFn_x3f_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_addFn_x3f_1331_, 1);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_val_1332_);
v___x_1334_ = v___x_1328_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_val_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v_type_1336_; lean_object* v_u_1337_; lean_object* v_semiringInst_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_expectedInst_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1328_);
v_type_1336_ = lean_ctor_get(v_toRing_1330_, 1);
lean_inc_ref_n(v_type_1336_, 3);
v_u_1337_ = lean_ctor_get(v_toRing_1330_, 2);
lean_inc_n(v_u_1337_, 2);
v_semiringInst_1338_ = lean_ctor_get(v_toRing_1330_, 4);
lean_inc_ref(v_semiringInst_1338_);
lean_dec_ref(v_toRing_1330_);
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_u_1337_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
lean_inc_ref(v___x_1341_);
v___x_1342_ = l_Lean_mkConst(v___x_1339_, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3));
v___x_1344_ = l_Lean_mkConst(v___x_1343_, v___x_1341_);
v___x_1345_ = l_Lean_mkAppB(v___x_1344_, v_type_1336_, v_semiringInst_1338_);
v_expectedInst_1346_ = l_Lean_mkAppB(v___x_1342_, v_type_1336_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5));
v___x_1348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7));
v___x_1349_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1336_, v_u_1337_, v___x_1347_, v___x_1348_, v_expectedInst_1346_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_a_1350_, 2);
lean_dec_ref_known(v___x_1349_, 1);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_1351_, 0, v_a_1350_);
v___x_1352_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1351_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1360_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_a_1350_);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1350_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1350_);
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1325_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1325_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1391_, lean_object* v_acc_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
if (lean_obj_tag(v_p_1391_) == 0)
{
lean_object* v_k_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1426_; 
v_k_1405_ = lean_ctor_get(v_p_1391_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_p_1391_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1407_ = v_p_1391_;
v_isShared_1408_ = v_isSharedCheck_1426_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_k_1405_);
lean_dec(v_p_1391_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1426_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1410_ = lean_int_dec_eq(v_k_1405_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_del_object(v___x_1407_);
v___x_1411_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1405_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v_k_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = l_Lean_mkAppB(v_a_1412_, v_acc_1392_, v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_dec(v_a_1412_);
lean_dec_ref(v_acc_1392_);
return v___x_1413_;
}
}
else
{
lean_dec(v_k_1405_);
lean_dec_ref(v_acc_1392_);
return v___x_1411_;
}
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_k_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v_acc_1392_);
v___x_1424_ = v___x_1407_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_acc_1392_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_k_1427_; lean_object* v_v_1428_; lean_object* v_p_1429_; lean_object* v___x_1430_; 
v_k_1427_ = lean_ctor_get(v_p_1391_, 0);
lean_inc(v_k_1427_);
v_v_1428_ = lean_ctor_get(v_p_1391_, 1);
lean_inc(v_v_1428_);
v_p_1429_ = lean_ctor_get(v_p_1391_, 2);
lean_inc_ref(v_p_1429_);
lean_dec_ref_known(v_p_1391_, 3);
v___x_1430_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1427_, v_v_1428_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v_k_1427_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l_Lean_mkAppB(v_a_1431_, v_acc_1392_, v_a_1433_);
v_p_1391_ = v_p_1429_;
v_acc_1392_ = v___x_1434_;
goto _start;
}
else
{
lean_dec(v_a_1431_);
lean_dec_ref(v_p_1429_);
lean_dec_ref(v_acc_1392_);
return v___x_1432_;
}
}
else
{
lean_dec_ref(v_p_1429_);
lean_dec(v_v_1428_);
lean_dec(v_k_1427_);
lean_dec_ref(v_acc_1392_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1436_, lean_object* v_acc_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1436_, v_acc_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
if (lean_obj_tag(v_p_1451_) == 0)
{
lean_object* v_k_1464_; lean_object* v___x_1465_; 
v_k_1464_ = lean_ctor_get(v_p_1451_, 0);
lean_inc(v_k_1464_);
lean_dec_ref_known(v_p_1451_, 1);
v___x_1465_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1464_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v_k_1464_);
return v___x_1465_;
}
else
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v_p_1468_; lean_object* v___x_1469_; 
v_k_1466_ = lean_ctor_get(v_p_1451_, 0);
lean_inc(v_k_1466_);
v_v_1467_ = lean_ctor_get(v_p_1451_, 1);
lean_inc(v_v_1467_);
v_p_1468_ = lean_ctor_get(v_p_1451_, 2);
lean_inc_ref(v_p_1468_);
lean_dec_ref_known(v_p_1451_, 3);
v___x_1469_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1466_, v_v_1467_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v_k_1466_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1468_, v_a_1470_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1471_;
}
else
{
lean_dec_ref(v_p_1468_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1485_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1486_; double v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_float_of_nat(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_ref_1498_; lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1544_; 
v_ref_1498_ = lean_ctor_get(v___y_1495_, 2);
v___x_1499_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1544_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1544_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v_traceState_1505_; lean_object* v_env_1506_; lean_object* v_nextMacroScope_1507_; lean_object* v_ngen_1508_; lean_object* v_auxDeclNGen_1509_; lean_object* v_cache_1510_; lean_object* v_messages_1511_; lean_object* v_infoState_1512_; lean_object* v_snapshotTasks_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1543_; 
v___x_1504_ = lean_st_ref_take(v___y_1496_);
v_traceState_1505_ = lean_ctor_get(v___x_1504_, 4);
v_env_1506_ = lean_ctor_get(v___x_1504_, 0);
v_nextMacroScope_1507_ = lean_ctor_get(v___x_1504_, 1);
v_ngen_1508_ = lean_ctor_get(v___x_1504_, 2);
v_auxDeclNGen_1509_ = lean_ctor_get(v___x_1504_, 3);
v_cache_1510_ = lean_ctor_get(v___x_1504_, 5);
v_messages_1511_ = lean_ctor_get(v___x_1504_, 6);
v_infoState_1512_ = lean_ctor_get(v___x_1504_, 7);
v_snapshotTasks_1513_ = lean_ctor_get(v___x_1504_, 8);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1515_ = v___x_1504_;
v_isShared_1516_ = v_isSharedCheck_1543_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snapshotTasks_1513_);
lean_inc(v_infoState_1512_);
lean_inc(v_messages_1511_);
lean_inc(v_cache_1510_);
lean_inc(v_traceState_1505_);
lean_inc(v_auxDeclNGen_1509_);
lean_inc(v_ngen_1508_);
lean_inc(v_nextMacroScope_1507_);
lean_inc(v_env_1506_);
lean_dec(v___x_1504_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1543_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint64_t v_tid_1517_; lean_object* v_traces_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1542_; 
v_tid_1517_ = lean_ctor_get_uint64(v_traceState_1505_, sizeof(void*)*1);
v_traces_1518_ = lean_ctor_get(v_traceState_1505_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_traceState_1505_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1520_ = v_traceState_1505_;
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_traces_1518_);
lean_dec(v_traceState_1505_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; double v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1524_ = 0;
v___x_1525_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1526_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1526_, 0, v_cls_1491_);
lean_ctor_set(v___x_1526_, 1, v___x_1522_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
lean_ctor_set_float(v___x_1526_, sizeof(void*)*3, v___x_1523_);
lean_ctor_set_float(v___x_1526_, sizeof(void*)*3 + 8, v___x_1523_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*3 + 16, v___x_1524_);
v___x_1527_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1528_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v_a_1500_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
lean_inc(v_ref_1498_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_ref_1498_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l_Lean_PersistentArray_push___redArg(v_traces_1518_, v___x_1529_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1530_);
v___x_1532_ = v___x_1520_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1530_);
lean_ctor_set_uint64(v_reuseFailAlloc_1541_, sizeof(void*)*1, v_tid_1517_);
v___x_1532_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 4, v___x_1532_);
v___x_1534_ = v___x_1515_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_env_1506_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_nextMacroScope_1507_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_ngen_1508_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_auxDeclNGen_1509_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v_cache_1510_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_messages_1511_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_infoState_1512_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_snapshotTasks_1513_);
v___x_1534_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = lean_st_ref_put(v___y_1496_, v___x_1534_);
v___x_1536_ = lean_box(0);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1536_);
v___x_1538_ = v___x_1502_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1545_, v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1552_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1568_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1569_ = l_Lean_Name_append(v___x_1568_, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1573_, v_a_1574_, v_a_1582_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1812_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1812_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1812_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_unbox(v_a_1586_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v___x_1591_ = lean_box(0);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v___x_1595_; 
lean_del_object(v___x_1588_);
v___x_1595_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1803_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1803_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1803_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_a_1596_) == 1)
{
lean_object* v_val_1600_; lean_object* v___x_1601_; 
lean_del_object(v___x_1598_);
v_val_1600_ = lean_ctor_get(v_a_1596_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_a_1596_, 1);
lean_inc_ref(v_p_1573_);
v___x_1601_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1573_, v_a_1574_, v_a_1582_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_Meta_Sym_canon(v_a_1602_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = l_Lean_Meta_Sym_shareCommon(v_a_1604_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
lean_inc_ref(v_p_1573_);
v___x_1607_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1573_, v_a_1574_, v_a_1582_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_n(v_a_1608_, 2);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = 0;
v___x_1610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1610_, 0, v_val_1600_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*1, v___x_1609_);
v___x_1611_ = lean_unbox(v_a_1586_);
v___x_1612_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1606_, v___x_1611_, v_a_1608_, v___x_1610_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1758_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1758_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1758_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
if (lean_obj_tag(v_a_1613_) == 1)
{
lean_object* v_val_1617_; lean_object* v___x_1618_; 
lean_del_object(v___x_1615_);
v_val_1617_ = lean_ctor_get(v_a_1613_, 0);
lean_inc_n(v_val_1617_, 2);
lean_dec_ref_known(v_a_1613_, 1);
v___x_1618_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_val_1617_, v___x_1610_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1745_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1745_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1745_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
if (lean_obj_tag(v_a_1619_) == 1)
{
lean_object* v_val_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1740_; 
lean_del_object(v___x_1621_);
v_val_1623_ = lean_ctor_get(v_a_1619_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1625_ = v_a_1619_;
v_isShared_1626_ = v_isSharedCheck_1740_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_val_1623_);
lean_dec(v_a_1619_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1740_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; 
lean_inc(v_val_1623_);
v___x_1627_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1623_, v___x_1610_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec_ref_known(v___x_1610_, 1);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1628_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc_n(v_a_1630_, 2);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc(v_a_1575_);
lean_inc(v_a_1574_);
v___x_1632_ = lean_grind_internalize(v_a_1630_, v_a_1608_, v___x_1631_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1714_; 
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1715_);
v___x_1634_ = v___x_1632_;
v_isShared_1635_ = v_isSharedCheck_1714_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v___x_1632_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1714_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1630_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1705_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1705_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1705_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1573_, v_a_1637_);
if (v___x_1650_ == 0)
{
lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_del_object(v___x_1634_);
v___f_1651_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1651_, 0, v_a_1586_);
v___x_1652_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1653_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1652_, v___f_1651_, v_a_1574_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_toCold_1654_; lean_object* v_options_1655_; uint8_t v_hasTrace_1656_; 
lean_dec_ref_known(v___x_1653_, 1);
v_toCold_1654_ = lean_ctor_get(v_a_1582_, 0);
v_options_1655_ = lean_ctor_get(v_toCold_1654_, 2);
v_hasTrace_1656_ = lean_ctor_get_uint8(v_options_1655_, sizeof(void*)*1);
if (v_hasTrace_1656_ == 0)
{
lean_dec_ref(v_p_1573_);
goto v___jp_1641_;
}
else
{
lean_object* v_inheritedTraceOptions_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_inheritedTraceOptions_1657_ = lean_ctor_get(v_toCold_1654_, 11);
v___x_1658_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1659_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1657_, v_options_1655_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_dec_ref(v_p_1573_);
goto v___jp_1641_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1573_, v_a_1574_, v_a_1582_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
lean_inc(v_a_1637_);
v___x_1663_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1637_, v_a_1574_, v_a_1582_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_a_1662_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_a_1664_);
v___x_1668_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1658_, v___x_1667_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_dec_ref_known(v___x_1668_, 1);
goto v___jp_1641_;
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_a_1662_);
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
v_a_1677_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1663_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1663_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
v_a_1685_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1661_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1661_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec_ref(v_p_1573_);
v_a_1693_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1653_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1653_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v___x_1701_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1701_);
v___x_1703_ = v___x_1634_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
v___jp_1641_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_val_1623_);
lean_ctor_set(v___x_1642_, 1, v_a_1637_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_val_1617_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1643_);
v___x_1645_ = v___x_1625_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1647_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1645_);
v___x_1647_ = v___x_1639_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_del_object(v___x_1634_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1706_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1636_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1636_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1630_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1716_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1632_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1632_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1724_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1629_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1629_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_del_object(v___x_1625_);
lean_dec(v_val_1623_);
lean_dec(v_val_1617_);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1732_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1627_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1627_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_dec(v_a_1619_);
lean_dec(v_val_1617_);
lean_dec_ref_known(v___x_1610_, 1);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v___x_1741_ = lean_box(0);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1741_);
v___x_1743_ = v___x_1621_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_val_1617_);
lean_dec_ref_known(v___x_1610_, 1);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1746_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1618_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1618_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec(v_a_1613_);
lean_dec_ref_known(v___x_1610_, 1);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v___x_1754_ = lean_box(0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1754_);
v___x_1756_ = v___x_1615_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref_known(v___x_1610_, 1);
lean_dec(v_a_1608_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1759_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1612_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1612_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1606_);
lean_dec(v_val_1600_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1767_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1607_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1607_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_val_1600_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1775_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1605_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1605_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_val_1600_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1783_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1603_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1603_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_val_1600_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1791_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1601_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1601_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_dec(v_a_1596_);
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v___x_1799_ = lean_box(0);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1799_);
v___x_1801_ = v___x_1598_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1586_);
lean_dec_ref(v_p_1573_);
v_a_1804_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1595_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1595_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_p_1573_);
v_a_1813_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1585_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1585_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec(v_a_1822_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1834_, lean_object* v_msg_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1834_, v_msg_1835_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1849_, lean_object* v_msg_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1849_, v_msg_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1865_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1879_, lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1879_, v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1893_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
