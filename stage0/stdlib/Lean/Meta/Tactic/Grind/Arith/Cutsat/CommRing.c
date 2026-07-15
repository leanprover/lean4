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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_254_, lean_object* v_s_255_){
_start:
{
uint8_t v_a_152991__boxed_256_; lean_object* v_res_257_; 
v_a_152991__boxed_256_ = lean_unbox(v_a_254_);
v_res_257_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_152991__boxed_256_, v_s_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_258_, lean_object* v_s_259_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_ref_339_; lean_object* v___x_340_; lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_ref_339_ = lean_ctor_get(v___y_336_, 5);
v___x_340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
lean_inc_ref(v_type_360_);
v___x_373_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_360_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
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
lean_dec_ref_known(v_a_374_, 1);
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
v___x_382_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_383_ = l_Lean_indentExpr(v_type_360_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_384_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_409_, lean_object* v_u_410_, lean_object* v_instDeclName_411_, lean_object* v_declName_412_, lean_object* v_expectedInst_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
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
v___x_430_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_429_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_n(v_a_431_, 2);
lean_dec_ref_known(v___x_430_, 1);
lean_inc(v_declName_412_);
v___x_432_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_412_, v_a_431_, v_expectedInst_413_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref_known(v___x_432_, 1);
v___x_433_ = l_Lean_mkConst(v_declName_412_, v___x_427_);
v___x_434_ = l_Lean_mkAppB(v___x_433_, v_type_409_, v_a_431_);
v___x_435_ = l_Lean_Meta_Sym_canon(v___x_434_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l_Lean_Meta_Sym_shareCommon(v_a_436_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
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
lean_dec_ref_known(v___x_427_, 2);
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
lean_dec_ref_known(v___x_427_, 2);
lean_dec_ref(v_expectedInst_413_);
lean_dec(v_declName_412_);
lean_dec_ref(v_type_409_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
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
v_res_463_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_446_, v_u_447_, v_instDeclName_448_, v_declName_449_, v_expectedInst_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
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
lean_dec_ref_known(v_negFn_x3f_498_, 1);
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
v___x_506_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_u_504_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_mkConst(v___x_506_, v___x_508_);
v_expectedInst_510_ = l_Lean_mkAppB(v___x_509_, v_type_503_, v_ringInst_505_);
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8));
v___x_513_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_503_, v_u_504_, v___x_511_, v___x_512_, v_expectedInst_510_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_n(v_a_514_, 2);
lean_dec_ref_known(v___x_513_, 1);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_nat_to_int(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_toRing_585_; lean_object* v_type_586_; lean_object* v_u_587_; lean_object* v_semiringInst_588_; lean_object* v___x_589_; lean_object* v_n_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
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
v___x_591_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
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
lean_dec_ref_known(v_a_598_, 1);
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
v___x_634_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6));
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
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_593_);
v_n_617_ = l_Lean_mkApp3(v___x_616_, v_type_586_, v_n_590_, v_ofNatInst_603_);
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
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
v___x_623_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
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
lean_dec_ref_known(v___x_593_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_668_, lean_object* v_u_669_, lean_object* v_instDeclName_670_, lean_object* v_declName_671_, lean_object* v_expectedInst_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_685_ = lean_box(0);
lean_inc_n(v_u_669_, 2);
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v_u_669_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v_u_669_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_u_669_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
lean_inc_ref(v___x_688_);
v___x_689_ = l_Lean_mkConst(v_instDeclName_670_, v___x_688_);
lean_inc_ref_n(v_type_668_, 3);
v___x_690_ = l_Lean_mkApp3(v___x_689_, v_type_668_, v_type_668_, v_type_668_);
v___x_691_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_690_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_n(v_a_692_, 2);
lean_dec_ref_known(v___x_691_, 1);
lean_inc(v_declName_671_);
v___x_693_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_671_, v_a_692_, v_expectedInst_672_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref_known(v___x_693_, 1);
v___x_694_ = l_Lean_mkConst(v_declName_671_, v___x_688_);
lean_inc_ref_n(v_type_668_, 2);
v___x_695_ = l_Lean_mkApp4(v___x_694_, v_type_668_, v_type_668_, v_type_668_, v_a_692_);
v___x_696_ = l_Lean_Meta_Sym_canon(v___x_695_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_Meta_Sym_shareCommon(v_a_697_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_698_;
}
else
{
return v___x_696_;
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_692_);
lean_dec_ref_known(v___x_688_, 2);
lean_dec(v_declName_671_);
lean_dec_ref(v_type_668_);
v_a_699_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_693_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_693_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_688_, 2);
lean_dec_ref(v_expectedInst_672_);
lean_dec(v_declName_671_);
lean_dec_ref(v_type_668_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_707_ = _args[0];
lean_object* v_u_708_ = _args[1];
lean_object* v_instDeclName_709_ = _args[2];
lean_object* v_declName_710_ = _args[3];
lean_object* v_expectedInst_711_ = _args[4];
lean_object* v___y_712_ = _args[5];
lean_object* v___y_713_ = _args[6];
lean_object* v___y_714_ = _args[7];
lean_object* v___y_715_ = _args[8];
lean_object* v___y_716_ = _args[9];
lean_object* v___y_717_ = _args[10];
lean_object* v___y_718_ = _args[11];
lean_object* v___y_719_ = _args[12];
lean_object* v___y_720_ = _args[13];
lean_object* v___y_721_ = _args[14];
lean_object* v___y_722_ = _args[15];
lean_object* v___y_723_ = _args[16];
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_707_, v_u_708_, v_instDeclName_709_, v_declName_710_, v_expectedInst_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_725_, lean_object* v_s_726_){
_start:
{
lean_object* v_toRing_727_; lean_object* v_invFn_x3f_728_; lean_object* v_semiringId_x3f_729_; lean_object* v_commSemiringInst_730_; lean_object* v_commRingInst_731_; lean_object* v_noZeroDivInst_x3f_732_; lean_object* v_fieldInst_x3f_733_; lean_object* v_powIdentityInst_x3f_734_; lean_object* v_denoteEntries_735_; lean_object* v_nextId_736_; lean_object* v_steps_737_; lean_object* v_queue_738_; lean_object* v_basis_739_; lean_object* v_diseqs_740_; uint8_t v_recheck_741_; lean_object* v_invSet_742_; lean_object* v_powIdentityVarCount_743_; lean_object* v_numEq0_x3f_744_; uint8_t v_numEq0Updated_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_777_; 
v_toRing_727_ = lean_ctor_get(v_s_726_, 0);
v_invFn_x3f_728_ = lean_ctor_get(v_s_726_, 1);
v_semiringId_x3f_729_ = lean_ctor_get(v_s_726_, 2);
v_commSemiringInst_730_ = lean_ctor_get(v_s_726_, 3);
v_commRingInst_731_ = lean_ctor_get(v_s_726_, 4);
v_noZeroDivInst_x3f_732_ = lean_ctor_get(v_s_726_, 5);
v_fieldInst_x3f_733_ = lean_ctor_get(v_s_726_, 6);
v_powIdentityInst_x3f_734_ = lean_ctor_get(v_s_726_, 7);
v_denoteEntries_735_ = lean_ctor_get(v_s_726_, 8);
v_nextId_736_ = lean_ctor_get(v_s_726_, 9);
v_steps_737_ = lean_ctor_get(v_s_726_, 10);
v_queue_738_ = lean_ctor_get(v_s_726_, 11);
v_basis_739_ = lean_ctor_get(v_s_726_, 12);
v_diseqs_740_ = lean_ctor_get(v_s_726_, 13);
v_recheck_741_ = lean_ctor_get_uint8(v_s_726_, sizeof(void*)*17);
v_invSet_742_ = lean_ctor_get(v_s_726_, 14);
v_powIdentityVarCount_743_ = lean_ctor_get(v_s_726_, 15);
v_numEq0_x3f_744_ = lean_ctor_get(v_s_726_, 16);
v_numEq0Updated_745_ = lean_ctor_get_uint8(v_s_726_, sizeof(void*)*17 + 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_s_726_);
if (v_isSharedCheck_777_ == 0)
{
v___x_747_ = v_s_726_;
v_isShared_748_ = v_isSharedCheck_777_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_numEq0_x3f_744_);
lean_inc(v_powIdentityVarCount_743_);
lean_inc(v_invSet_742_);
lean_inc(v_diseqs_740_);
lean_inc(v_basis_739_);
lean_inc(v_queue_738_);
lean_inc(v_steps_737_);
lean_inc(v_nextId_736_);
lean_inc(v_denoteEntries_735_);
lean_inc(v_powIdentityInst_x3f_734_);
lean_inc(v_fieldInst_x3f_733_);
lean_inc(v_noZeroDivInst_x3f_732_);
lean_inc(v_commRingInst_731_);
lean_inc(v_commSemiringInst_730_);
lean_inc(v_semiringId_x3f_729_);
lean_inc(v_invFn_x3f_728_);
lean_inc(v_toRing_727_);
lean_dec(v_s_726_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_777_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_id_749_; lean_object* v_type_750_; lean_object* v_u_751_; lean_object* v_ringInst_752_; lean_object* v_semiringInst_753_; lean_object* v_charInst_x3f_754_; lean_object* v_addFn_x3f_755_; lean_object* v_subFn_x3f_756_; lean_object* v_negFn_x3f_757_; lean_object* v_powFn_x3f_758_; lean_object* v_intCastFn_x3f_759_; lean_object* v_natCastFn_x3f_760_; lean_object* v_one_x3f_761_; lean_object* v_vars_762_; lean_object* v_varMap_763_; lean_object* v_denote_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_775_; 
v_id_749_ = lean_ctor_get(v_toRing_727_, 0);
v_type_750_ = lean_ctor_get(v_toRing_727_, 1);
v_u_751_ = lean_ctor_get(v_toRing_727_, 2);
v_ringInst_752_ = lean_ctor_get(v_toRing_727_, 3);
v_semiringInst_753_ = lean_ctor_get(v_toRing_727_, 4);
v_charInst_x3f_754_ = lean_ctor_get(v_toRing_727_, 5);
v_addFn_x3f_755_ = lean_ctor_get(v_toRing_727_, 6);
v_subFn_x3f_756_ = lean_ctor_get(v_toRing_727_, 8);
v_negFn_x3f_757_ = lean_ctor_get(v_toRing_727_, 9);
v_powFn_x3f_758_ = lean_ctor_get(v_toRing_727_, 10);
v_intCastFn_x3f_759_ = lean_ctor_get(v_toRing_727_, 11);
v_natCastFn_x3f_760_ = lean_ctor_get(v_toRing_727_, 12);
v_one_x3f_761_ = lean_ctor_get(v_toRing_727_, 13);
v_vars_762_ = lean_ctor_get(v_toRing_727_, 14);
v_varMap_763_ = lean_ctor_get(v_toRing_727_, 15);
v_denote_764_ = lean_ctor_get(v_toRing_727_, 16);
v_isSharedCheck_775_ = !lean_is_exclusive(v_toRing_727_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_toRing_727_, 7);
lean_dec(v_unused_776_);
v___x_766_ = v_toRing_727_;
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_denote_764_);
lean_inc(v_varMap_763_);
lean_inc(v_vars_762_);
lean_inc(v_one_x3f_761_);
lean_inc(v_natCastFn_x3f_760_);
lean_inc(v_intCastFn_x3f_759_);
lean_inc(v_powFn_x3f_758_);
lean_inc(v_negFn_x3f_757_);
lean_inc(v_subFn_x3f_756_);
lean_inc(v_addFn_x3f_755_);
lean_inc(v_charInst_x3f_754_);
lean_inc(v_semiringInst_753_);
lean_inc(v_ringInst_752_);
lean_inc(v_u_751_);
lean_inc(v_type_750_);
lean_inc(v_id_749_);
lean_dec(v_toRing_727_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v_a_725_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 7, v___x_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_id_749_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_type_750_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_u_751_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_ringInst_752_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_semiringInst_753_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_charInst_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_addFn_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_774_, 7, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_774_, 8, v_subFn_x3f_756_);
lean_ctor_set(v_reuseFailAlloc_774_, 9, v_negFn_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_774_, 10, v_powFn_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 11, v_intCastFn_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 12, v_natCastFn_x3f_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 13, v_one_x3f_761_);
lean_ctor_set(v_reuseFailAlloc_774_, 14, v_vars_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 15, v_varMap_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 16, v_denote_764_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_770_);
v___x_772_ = v___x_747_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_invFn_x3f_728_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_semiringId_x3f_729_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_commSemiringInst_730_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_commRingInst_731_);
lean_ctor_set(v_reuseFailAlloc_773_, 5, v_noZeroDivInst_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_773_, 6, v_fieldInst_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_773_, 7, v_powIdentityInst_x3f_734_);
lean_ctor_set(v_reuseFailAlloc_773_, 8, v_denoteEntries_735_);
lean_ctor_set(v_reuseFailAlloc_773_, 9, v_nextId_736_);
lean_ctor_set(v_reuseFailAlloc_773_, 10, v_steps_737_);
lean_ctor_set(v_reuseFailAlloc_773_, 11, v_queue_738_);
lean_ctor_set(v_reuseFailAlloc_773_, 12, v_basis_739_);
lean_ctor_set(v_reuseFailAlloc_773_, 13, v_diseqs_740_);
lean_ctor_set(v_reuseFailAlloc_773_, 14, v_invSet_742_);
lean_ctor_set(v_reuseFailAlloc_773_, 15, v_powIdentityVarCount_743_);
lean_ctor_set(v_reuseFailAlloc_773_, 16, v_numEq0_x3f_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_773_, sizeof(void*)*17, v_recheck_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_773_, sizeof(void*)*17 + 1, v_numEq0Updated_745_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_845_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_845_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_toRing_806_; lean_object* v_mulFn_x3f_807_; 
v_toRing_806_ = lean_ctor_get(v_a_802_, 0);
lean_inc_ref(v_toRing_806_);
lean_dec(v_a_802_);
v_mulFn_x3f_807_ = lean_ctor_get(v_toRing_806_, 7);
if (lean_obj_tag(v_mulFn_x3f_807_) == 1)
{
lean_object* v_val_808_; lean_object* v___x_810_; 
lean_inc_ref(v_mulFn_x3f_807_);
lean_dec_ref(v_toRing_806_);
v_val_808_ = lean_ctor_get(v_mulFn_x3f_807_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v_mulFn_x3f_807_, 1);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_val_808_);
v___x_810_ = v___x_804_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_val_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v_type_812_; lean_object* v_u_813_; lean_object* v_semiringInst_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_expectedInst_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_del_object(v___x_804_);
v_type_812_ = lean_ctor_get(v_toRing_806_, 1);
lean_inc_ref_n(v_type_812_, 3);
v_u_813_ = lean_ctor_get(v_toRing_806_, 2);
lean_inc_n(v_u_813_, 2);
v_semiringInst_814_ = lean_ctor_get(v_toRing_806_, 4);
lean_inc_ref(v_semiringInst_814_);
lean_dec_ref(v_toRing_806_);
v___x_815_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v_u_813_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
lean_inc_ref(v___x_817_);
v___x_818_ = l_Lean_mkConst(v___x_815_, v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_820_ = l_Lean_mkConst(v___x_819_, v___x_817_);
v___x_821_ = l_Lean_mkAppB(v___x_820_, v_type_812_, v_semiringInst_814_);
v_expectedInst_822_ = l_Lean_mkAppB(v___x_818_, v_type_812_, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_824_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_825_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_812_, v_u_813_, v___x_823_, v___x_824_, v_expectedInst_822_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___f_827_; lean_object* v___x_828_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc_n(v_a_826_, 2);
lean_dec_ref_known(v___x_825_, 1);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_827_, 0, v_a_826_);
v___x_828_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_827_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_836_);
v___x_830_ = v___x_828_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_dec(v___x_828_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_a_826_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_826_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_826_);
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_801_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_801_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_867_, lean_object* v_s_868_){
_start:
{
lean_object* v_toRing_869_; lean_object* v_invFn_x3f_870_; lean_object* v_semiringId_x3f_871_; lean_object* v_commSemiringInst_872_; lean_object* v_commRingInst_873_; lean_object* v_noZeroDivInst_x3f_874_; lean_object* v_fieldInst_x3f_875_; lean_object* v_powIdentityInst_x3f_876_; lean_object* v_denoteEntries_877_; lean_object* v_nextId_878_; lean_object* v_steps_879_; lean_object* v_queue_880_; lean_object* v_basis_881_; lean_object* v_diseqs_882_; uint8_t v_recheck_883_; lean_object* v_invSet_884_; lean_object* v_powIdentityVarCount_885_; lean_object* v_numEq0_x3f_886_; uint8_t v_numEq0Updated_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_919_; 
v_toRing_869_ = lean_ctor_get(v_s_868_, 0);
v_invFn_x3f_870_ = lean_ctor_get(v_s_868_, 1);
v_semiringId_x3f_871_ = lean_ctor_get(v_s_868_, 2);
v_commSemiringInst_872_ = lean_ctor_get(v_s_868_, 3);
v_commRingInst_873_ = lean_ctor_get(v_s_868_, 4);
v_noZeroDivInst_x3f_874_ = lean_ctor_get(v_s_868_, 5);
v_fieldInst_x3f_875_ = lean_ctor_get(v_s_868_, 6);
v_powIdentityInst_x3f_876_ = lean_ctor_get(v_s_868_, 7);
v_denoteEntries_877_ = lean_ctor_get(v_s_868_, 8);
v_nextId_878_ = lean_ctor_get(v_s_868_, 9);
v_steps_879_ = lean_ctor_get(v_s_868_, 10);
v_queue_880_ = lean_ctor_get(v_s_868_, 11);
v_basis_881_ = lean_ctor_get(v_s_868_, 12);
v_diseqs_882_ = lean_ctor_get(v_s_868_, 13);
v_recheck_883_ = lean_ctor_get_uint8(v_s_868_, sizeof(void*)*17);
v_invSet_884_ = lean_ctor_get(v_s_868_, 14);
v_powIdentityVarCount_885_ = lean_ctor_get(v_s_868_, 15);
v_numEq0_x3f_886_ = lean_ctor_get(v_s_868_, 16);
v_numEq0Updated_887_ = lean_ctor_get_uint8(v_s_868_, sizeof(void*)*17 + 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_s_868_);
if (v_isSharedCheck_919_ == 0)
{
v___x_889_ = v_s_868_;
v_isShared_890_ = v_isSharedCheck_919_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_numEq0_x3f_886_);
lean_inc(v_powIdentityVarCount_885_);
lean_inc(v_invSet_884_);
lean_inc(v_diseqs_882_);
lean_inc(v_basis_881_);
lean_inc(v_queue_880_);
lean_inc(v_steps_879_);
lean_inc(v_nextId_878_);
lean_inc(v_denoteEntries_877_);
lean_inc(v_powIdentityInst_x3f_876_);
lean_inc(v_fieldInst_x3f_875_);
lean_inc(v_noZeroDivInst_x3f_874_);
lean_inc(v_commRingInst_873_);
lean_inc(v_commSemiringInst_872_);
lean_inc(v_semiringId_x3f_871_);
lean_inc(v_invFn_x3f_870_);
lean_inc(v_toRing_869_);
lean_dec(v_s_868_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_919_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_id_891_; lean_object* v_type_892_; lean_object* v_u_893_; lean_object* v_ringInst_894_; lean_object* v_semiringInst_895_; lean_object* v_charInst_x3f_896_; lean_object* v_addFn_x3f_897_; lean_object* v_mulFn_x3f_898_; lean_object* v_subFn_x3f_899_; lean_object* v_negFn_x3f_900_; lean_object* v_intCastFn_x3f_901_; lean_object* v_natCastFn_x3f_902_; lean_object* v_one_x3f_903_; lean_object* v_vars_904_; lean_object* v_varMap_905_; lean_object* v_denote_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v_id_891_ = lean_ctor_get(v_toRing_869_, 0);
v_type_892_ = lean_ctor_get(v_toRing_869_, 1);
v_u_893_ = lean_ctor_get(v_toRing_869_, 2);
v_ringInst_894_ = lean_ctor_get(v_toRing_869_, 3);
v_semiringInst_895_ = lean_ctor_get(v_toRing_869_, 4);
v_charInst_x3f_896_ = lean_ctor_get(v_toRing_869_, 5);
v_addFn_x3f_897_ = lean_ctor_get(v_toRing_869_, 6);
v_mulFn_x3f_898_ = lean_ctor_get(v_toRing_869_, 7);
v_subFn_x3f_899_ = lean_ctor_get(v_toRing_869_, 8);
v_negFn_x3f_900_ = lean_ctor_get(v_toRing_869_, 9);
v_intCastFn_x3f_901_ = lean_ctor_get(v_toRing_869_, 11);
v_natCastFn_x3f_902_ = lean_ctor_get(v_toRing_869_, 12);
v_one_x3f_903_ = lean_ctor_get(v_toRing_869_, 13);
v_vars_904_ = lean_ctor_get(v_toRing_869_, 14);
v_varMap_905_ = lean_ctor_get(v_toRing_869_, 15);
v_denote_906_ = lean_ctor_get(v_toRing_869_, 16);
v_isSharedCheck_917_ = !lean_is_exclusive(v_toRing_869_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_toRing_869_, 10);
lean_dec(v_unused_918_);
v___x_908_ = v_toRing_869_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_denote_906_);
lean_inc(v_varMap_905_);
lean_inc(v_vars_904_);
lean_inc(v_one_x3f_903_);
lean_inc(v_natCastFn_x3f_902_);
lean_inc(v_intCastFn_x3f_901_);
lean_inc(v_negFn_x3f_900_);
lean_inc(v_subFn_x3f_899_);
lean_inc(v_mulFn_x3f_898_);
lean_inc(v_addFn_x3f_897_);
lean_inc(v_charInst_x3f_896_);
lean_inc(v_semiringInst_895_);
lean_inc(v_ringInst_894_);
lean_inc(v_u_893_);
lean_inc(v_type_892_);
lean_inc(v_id_891_);
lean_dec(v_toRing_869_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_a_867_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 10, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_id_891_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_type_892_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_u_893_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_ringInst_894_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_semiringInst_895_);
lean_ctor_set(v_reuseFailAlloc_916_, 5, v_charInst_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_916_, 6, v_addFn_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_916_, 7, v_mulFn_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_916_, 8, v_subFn_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_916_, 9, v_negFn_x3f_900_);
lean_ctor_set(v_reuseFailAlloc_916_, 10, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 11, v_intCastFn_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_916_, 12, v_natCastFn_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_916_, 13, v_one_x3f_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 14, v_vars_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 15, v_varMap_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 16, v_denote_906_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_912_);
v___x_914_ = v___x_889_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_invFn_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_semiringId_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_commSemiringInst_872_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_commRingInst_873_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_noZeroDivInst_x3f_874_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_fieldInst_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_powIdentityInst_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_915_, 8, v_denoteEntries_877_);
lean_ctor_set(v_reuseFailAlloc_915_, 9, v_nextId_878_);
lean_ctor_set(v_reuseFailAlloc_915_, 10, v_steps_879_);
lean_ctor_set(v_reuseFailAlloc_915_, 11, v_queue_880_);
lean_ctor_set(v_reuseFailAlloc_915_, 12, v_basis_881_);
lean_ctor_set(v_reuseFailAlloc_915_, 13, v_diseqs_882_);
lean_ctor_set(v_reuseFailAlloc_915_, 14, v_invSet_884_);
lean_ctor_set(v_reuseFailAlloc_915_, 15, v_powIdentityVarCount_885_);
lean_ctor_set(v_reuseFailAlloc_915_, 16, v_numEq0_x3f_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*17, v_recheck_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*17 + 1, v_numEq0Updated_887_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = l_Lean_Level_ofNat(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_930_, lean_object* v_type_931_, lean_object* v_semiringInst_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_946_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_947_ = lean_box(0);
lean_inc(v_u_930_);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v_u_930_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
lean_inc_ref(v___x_948_);
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v_u_930_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
lean_inc_ref(v___x_950_);
v___x_951_ = l_Lean_mkConst(v___x_945_, v___x_950_);
v___x_952_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_931_, 2);
v___x_953_ = l_Lean_mkApp3(v___x_951_, v_type_931_, v___x_952_, v_type_931_);
v___x_954_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_953_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_inst_x27_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_n(v_a_955_, 2);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_957_ = l_Lean_mkConst(v___x_956_, v___x_948_);
lean_inc_ref(v_type_931_);
v_inst_x27_958_ = l_Lean_mkAppB(v___x_957_, v_type_931_, v_semiringInst_932_);
v___x_959_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_960_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_959_, v_a_955_, v_inst_x27_958_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref_known(v___x_960_, 1);
v___x_961_ = l_Lean_mkConst(v___x_959_, v___x_950_);
lean_inc_ref(v_type_931_);
v___x_962_ = l_Lean_mkApp4(v___x_961_, v_type_931_, v___x_952_, v_type_931_, v_a_955_);
v___x_963_ = l_Lean_Meta_Sym_canon(v___x_962_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = l_Lean_Meta_Sym_shareCommon(v_a_964_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_965_;
}
else
{
return v___x_963_;
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_955_);
lean_dec_ref_known(v___x_950_, 2);
lean_dec_ref(v_type_931_);
v_a_966_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_960_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_960_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_950_, 2);
lean_dec_ref_known(v___x_948_, 2);
lean_dec_ref(v_semiringInst_932_);
lean_dec_ref(v_type_931_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_974_, lean_object* v_type_975_, lean_object* v_semiringInst_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_974_, v_type_975_, v_semiringInst_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1036_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1036_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1036_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_toRing_1007_; lean_object* v_powFn_x3f_1008_; 
v_toRing_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc_ref(v_toRing_1007_);
lean_dec(v_a_1003_);
v_powFn_x3f_1008_ = lean_ctor_get(v_toRing_1007_, 10);
if (lean_obj_tag(v_powFn_x3f_1008_) == 1)
{
lean_object* v_val_1009_; lean_object* v___x_1011_; 
lean_inc_ref(v_powFn_x3f_1008_);
lean_dec_ref(v_toRing_1007_);
v_val_1009_ = lean_ctor_get(v_powFn_x3f_1008_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v_powFn_x3f_1008_, 1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_val_1009_);
v___x_1011_ = v___x_1005_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_val_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v_type_1013_; lean_object* v_u_1014_; lean_object* v_semiringInst_1015_; lean_object* v___x_1016_; 
lean_del_object(v___x_1005_);
v_type_1013_ = lean_ctor_get(v_toRing_1007_, 1);
lean_inc_ref(v_type_1013_);
v_u_1014_ = lean_ctor_get(v_toRing_1007_, 2);
lean_inc(v_u_1014_);
v_semiringInst_1015_ = lean_ctor_get(v_toRing_1007_, 4);
lean_inc_ref(v_semiringInst_1015_);
lean_dec_ref(v_toRing_1007_);
v___x_1016_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1014_, v_type_1013_, v_semiringInst_1015_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_n(v_a_1017_, 2);
lean_dec_ref_known(v___x_1016_, 1);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1018_, 0, v_a_1017_);
v___x_1019_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1018_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1027_);
v___x_1021_ = v___x_1019_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v___x_1019_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1017_);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1017_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_a_1017_);
v_a_1028_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1019_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1019_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1002_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1002_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1103_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1103_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1103_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_toRing_1076_; lean_object* v_vars_1077_; lean_object* v_x_1078_; lean_object* v_k_1079_; lean_object* v___y_1081_; lean_object* v_size_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_toRing_1076_ = lean_ctor_get(v_a_1072_, 0);
lean_inc_ref(v_toRing_1076_);
lean_dec(v_a_1072_);
v_vars_1077_ = lean_ctor_get(v_toRing_1076_, 14);
lean_inc_ref(v_vars_1077_);
lean_dec_ref(v_toRing_1076_);
v_x_1078_ = lean_ctor_get(v_pw_1058_, 0);
lean_inc(v_x_1078_);
v_k_1079_ = lean_ctor_get(v_pw_1058_, 1);
lean_inc(v_k_1079_);
lean_dec_ref(v_pw_1058_);
v_size_1098_ = lean_ctor_get(v_vars_1077_, 2);
v___x_1099_ = l_Lean_instInhabitedExpr;
v___x_1100_ = lean_nat_dec_lt(v_x_1078_, v_size_1098_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_x_1078_);
lean_dec_ref(v_vars_1077_);
v___x_1101_ = l_outOfBounds___redArg(v___x_1099_);
v___y_1081_ = v___x_1101_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1099_, v_vars_1077_, v_x_1078_);
lean_dec(v_x_1078_);
lean_dec_ref(v_vars_1077_);
v___y_1081_ = v___x_1102_;
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_nat_dec_eq(v_k_1079_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_del_object(v___x_1074_);
v___x_1084_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1094_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = l_Lean_mkNatLit(v_k_1079_);
v___x_1090_ = l_Lean_mkAppB(v_a_1085_, v___y_1081_, v___x_1089_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_dec_ref(v___y_1081_);
lean_dec(v_k_1079_);
return v___x_1084_;
}
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_k_1079_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___y_1081_);
v___x_1096_ = v___x_1074_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___y_1081_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_pw_1058_);
v_a_1104_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1071_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1071_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_m_1126_, lean_object* v_acc_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
if (lean_obj_tag(v_m_1126_) == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_acc_1127_);
return v___x_1140_;
}
else
{
lean_object* v_p_1141_; lean_object* v_m_1142_; lean_object* v___x_1143_; 
v_p_1141_ = lean_ctor_get(v_m_1126_, 0);
lean_inc_ref(v_p_1141_);
v_m_1142_ = lean_ctor_get(v_m_1126_, 1);
lean_inc(v_m_1142_);
lean_dec_ref_known(v_m_1126_, 2);
v___x_1143_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1141_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = l_Lean_mkAppB(v_a_1144_, v_acc_1127_, v_a_1146_);
v_m_1126_ = v_m_1142_;
v_acc_1127_ = v___x_1147_;
goto _start;
}
else
{
lean_dec(v_a_1144_);
lean_dec(v_m_1142_);
lean_dec_ref(v_acc_1127_);
return v___x_1145_;
}
}
else
{
lean_dec(v_m_1142_);
lean_dec_ref(v_p_1141_);
lean_dec_ref(v_acc_1127_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_m_1149_, lean_object* v_acc_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1149_, v_acc_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1163_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_to_int(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_m_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
if (lean_obj_tag(v_m_1166_) == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1180_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1179_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1180_;
}
else
{
lean_object* v_p_1181_; lean_object* v_m_1182_; lean_object* v___x_1183_; 
v_p_1181_ = lean_ctor_get(v_m_1166_, 0);
lean_inc_ref(v_p_1181_);
v_m_1182_ = lean_ctor_get(v_m_1166_, 1);
lean_inc(v_m_1182_);
lean_dec_ref_known(v_m_1166_, 2);
v___x_1183_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1181_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1182_, v_a_1184_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1185_;
}
else
{
lean_dec(v_m_1182_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_m_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1200_, lean_object* v_m_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1215_ = lean_int_dec_eq(v_k_1200_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1200_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_mkAppB(v_a_1217_, v_a_1219_, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_dec(v_a_1219_);
lean_dec(v_a_1217_);
return v___x_1220_;
}
}
else
{
lean_dec(v_a_1217_);
lean_dec(v_m_1201_);
return v___x_1218_;
}
}
else
{
lean_dec(v_m_1201_);
return v___x_1216_;
}
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1231_, lean_object* v_m_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1231_, v_m_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v_k_1231_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_1246_, lean_object* v_s_1247_){
_start:
{
lean_object* v_toRing_1248_; lean_object* v_invFn_x3f_1249_; lean_object* v_semiringId_x3f_1250_; lean_object* v_commSemiringInst_1251_; lean_object* v_commRingInst_1252_; lean_object* v_noZeroDivInst_x3f_1253_; lean_object* v_fieldInst_x3f_1254_; lean_object* v_powIdentityInst_x3f_1255_; lean_object* v_denoteEntries_1256_; lean_object* v_nextId_1257_; lean_object* v_steps_1258_; lean_object* v_queue_1259_; lean_object* v_basis_1260_; lean_object* v_diseqs_1261_; uint8_t v_recheck_1262_; lean_object* v_invSet_1263_; lean_object* v_powIdentityVarCount_1264_; lean_object* v_numEq0_x3f_1265_; uint8_t v_numEq0Updated_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1298_; 
v_toRing_1248_ = lean_ctor_get(v_s_1247_, 0);
v_invFn_x3f_1249_ = lean_ctor_get(v_s_1247_, 1);
v_semiringId_x3f_1250_ = lean_ctor_get(v_s_1247_, 2);
v_commSemiringInst_1251_ = lean_ctor_get(v_s_1247_, 3);
v_commRingInst_1252_ = lean_ctor_get(v_s_1247_, 4);
v_noZeroDivInst_x3f_1253_ = lean_ctor_get(v_s_1247_, 5);
v_fieldInst_x3f_1254_ = lean_ctor_get(v_s_1247_, 6);
v_powIdentityInst_x3f_1255_ = lean_ctor_get(v_s_1247_, 7);
v_denoteEntries_1256_ = lean_ctor_get(v_s_1247_, 8);
v_nextId_1257_ = lean_ctor_get(v_s_1247_, 9);
v_steps_1258_ = lean_ctor_get(v_s_1247_, 10);
v_queue_1259_ = lean_ctor_get(v_s_1247_, 11);
v_basis_1260_ = lean_ctor_get(v_s_1247_, 12);
v_diseqs_1261_ = lean_ctor_get(v_s_1247_, 13);
v_recheck_1262_ = lean_ctor_get_uint8(v_s_1247_, sizeof(void*)*17);
v_invSet_1263_ = lean_ctor_get(v_s_1247_, 14);
v_powIdentityVarCount_1264_ = lean_ctor_get(v_s_1247_, 15);
v_numEq0_x3f_1265_ = lean_ctor_get(v_s_1247_, 16);
v_numEq0Updated_1266_ = lean_ctor_get_uint8(v_s_1247_, sizeof(void*)*17 + 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_s_1247_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1268_ = v_s_1247_;
v_isShared_1269_ = v_isSharedCheck_1298_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_numEq0_x3f_1265_);
lean_inc(v_powIdentityVarCount_1264_);
lean_inc(v_invSet_1263_);
lean_inc(v_diseqs_1261_);
lean_inc(v_basis_1260_);
lean_inc(v_queue_1259_);
lean_inc(v_steps_1258_);
lean_inc(v_nextId_1257_);
lean_inc(v_denoteEntries_1256_);
lean_inc(v_powIdentityInst_x3f_1255_);
lean_inc(v_fieldInst_x3f_1254_);
lean_inc(v_noZeroDivInst_x3f_1253_);
lean_inc(v_commRingInst_1252_);
lean_inc(v_commSemiringInst_1251_);
lean_inc(v_semiringId_x3f_1250_);
lean_inc(v_invFn_x3f_1249_);
lean_inc(v_toRing_1248_);
lean_dec(v_s_1247_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1298_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_id_1270_; lean_object* v_type_1271_; lean_object* v_u_1272_; lean_object* v_ringInst_1273_; lean_object* v_semiringInst_1274_; lean_object* v_charInst_x3f_1275_; lean_object* v_mulFn_x3f_1276_; lean_object* v_subFn_x3f_1277_; lean_object* v_negFn_x3f_1278_; lean_object* v_powFn_x3f_1279_; lean_object* v_intCastFn_x3f_1280_; lean_object* v_natCastFn_x3f_1281_; lean_object* v_one_x3f_1282_; lean_object* v_vars_1283_; lean_object* v_varMap_1284_; lean_object* v_denote_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1296_; 
v_id_1270_ = lean_ctor_get(v_toRing_1248_, 0);
v_type_1271_ = lean_ctor_get(v_toRing_1248_, 1);
v_u_1272_ = lean_ctor_get(v_toRing_1248_, 2);
v_ringInst_1273_ = lean_ctor_get(v_toRing_1248_, 3);
v_semiringInst_1274_ = lean_ctor_get(v_toRing_1248_, 4);
v_charInst_x3f_1275_ = lean_ctor_get(v_toRing_1248_, 5);
v_mulFn_x3f_1276_ = lean_ctor_get(v_toRing_1248_, 7);
v_subFn_x3f_1277_ = lean_ctor_get(v_toRing_1248_, 8);
v_negFn_x3f_1278_ = lean_ctor_get(v_toRing_1248_, 9);
v_powFn_x3f_1279_ = lean_ctor_get(v_toRing_1248_, 10);
v_intCastFn_x3f_1280_ = lean_ctor_get(v_toRing_1248_, 11);
v_natCastFn_x3f_1281_ = lean_ctor_get(v_toRing_1248_, 12);
v_one_x3f_1282_ = lean_ctor_get(v_toRing_1248_, 13);
v_vars_1283_ = lean_ctor_get(v_toRing_1248_, 14);
v_varMap_1284_ = lean_ctor_get(v_toRing_1248_, 15);
v_denote_1285_ = lean_ctor_get(v_toRing_1248_, 16);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_toRing_1248_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v_toRing_1248_, 6);
lean_dec(v_unused_1297_);
v___x_1287_ = v_toRing_1248_;
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_denote_1285_);
lean_inc(v_varMap_1284_);
lean_inc(v_vars_1283_);
lean_inc(v_one_x3f_1282_);
lean_inc(v_natCastFn_x3f_1281_);
lean_inc(v_intCastFn_x3f_1280_);
lean_inc(v_powFn_x3f_1279_);
lean_inc(v_negFn_x3f_1278_);
lean_inc(v_subFn_x3f_1277_);
lean_inc(v_mulFn_x3f_1276_);
lean_inc(v_charInst_x3f_1275_);
lean_inc(v_semiringInst_1274_);
lean_inc(v_ringInst_1273_);
lean_inc(v_u_1272_);
lean_inc(v_type_1271_);
lean_inc(v_id_1270_);
lean_dec(v_toRing_1248_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_a_1246_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 6, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_id_1270_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_type_1271_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_u_1272_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_ringInst_1273_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_semiringInst_1274_);
lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_charInst_x3f_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 6, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_mulFn_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_subFn_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1295_, 9, v_negFn_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1295_, 10, v_powFn_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1295_, 11, v_intCastFn_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1295_, 12, v_natCastFn_x3f_1281_);
lean_ctor_set(v_reuseFailAlloc_1295_, 13, v_one_x3f_1282_);
lean_ctor_set(v_reuseFailAlloc_1295_, 14, v_vars_1283_);
lean_ctor_set(v_reuseFailAlloc_1295_, 15, v_varMap_1284_);
lean_ctor_set(v_reuseFailAlloc_1295_, 16, v_denote_1285_);
v___x_1291_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1291_);
v___x_1293_ = v___x_1268_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_invFn_x3f_1249_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_semiringId_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_commSemiringInst_1251_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_commRingInst_1252_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v_noZeroDivInst_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1294_, 6, v_fieldInst_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1294_, 7, v_powIdentityInst_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1294_, 8, v_denoteEntries_1256_);
lean_ctor_set(v_reuseFailAlloc_1294_, 9, v_nextId_1257_);
lean_ctor_set(v_reuseFailAlloc_1294_, 10, v_steps_1258_);
lean_ctor_set(v_reuseFailAlloc_1294_, 11, v_queue_1259_);
lean_ctor_set(v_reuseFailAlloc_1294_, 12, v_basis_1260_);
lean_ctor_set(v_reuseFailAlloc_1294_, 13, v_diseqs_1261_);
lean_ctor_set(v_reuseFailAlloc_1294_, 14, v_invSet_1263_);
lean_ctor_set(v_reuseFailAlloc_1294_, 15, v_powIdentityVarCount_1264_);
lean_ctor_set(v_reuseFailAlloc_1294_, 16, v_numEq0_x3f_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*17, v_recheck_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*17 + 1, v_numEq0Updated_1266_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1371_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1371_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1371_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v_toRing_1332_; lean_object* v_addFn_x3f_1333_; 
v_toRing_1332_ = lean_ctor_get(v_a_1328_, 0);
lean_inc_ref(v_toRing_1332_);
lean_dec(v_a_1328_);
v_addFn_x3f_1333_ = lean_ctor_get(v_toRing_1332_, 6);
if (lean_obj_tag(v_addFn_x3f_1333_) == 1)
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
lean_inc_ref(v_addFn_x3f_1333_);
lean_dec_ref(v_toRing_1332_);
v_val_1334_ = lean_ctor_get(v_addFn_x3f_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_addFn_x3f_1333_, 1);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_val_1334_);
v___x_1336_ = v___x_1330_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v_type_1338_; lean_object* v_u_1339_; lean_object* v_semiringInst_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_expectedInst_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_del_object(v___x_1330_);
v_type_1338_ = lean_ctor_get(v_toRing_1332_, 1);
lean_inc_ref_n(v_type_1338_, 3);
v_u_1339_ = lean_ctor_get(v_toRing_1332_, 2);
lean_inc_n(v_u_1339_, 2);
v_semiringInst_1340_ = lean_ctor_get(v_toRing_1332_, 4);
lean_inc_ref(v_semiringInst_1340_);
lean_dec_ref(v_toRing_1332_);
v___x_1341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_u_1339_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
lean_inc_ref(v___x_1343_);
v___x_1344_ = l_Lean_mkConst(v___x_1341_, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3));
v___x_1346_ = l_Lean_mkConst(v___x_1345_, v___x_1343_);
v___x_1347_ = l_Lean_mkAppB(v___x_1346_, v_type_1338_, v_semiringInst_1340_);
v_expectedInst_1348_ = l_Lean_mkAppB(v___x_1344_, v_type_1338_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5));
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7));
v___x_1351_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1338_, v_u_1339_, v___x_1349_, v___x_1350_, v_expectedInst_1348_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_n(v_a_1352_, 2);
lean_dec_ref_known(v___x_1351_, 1);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_1353_, 0, v_a_1352_);
v___x_1354_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1353_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1354_, 0);
lean_dec(v_unused_1362_);
v___x_1356_ = v___x_1354_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_a_1352_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1352_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1352_);
v_a_1363_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1354_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1354_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1327_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1327_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
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
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1393_, lean_object* v_acc_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
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
v___x_1411_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1412_ = lean_int_dec_eq(v_k_1407_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_del_object(v___x_1409_);
v___x_1413_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1407_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
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
lean_dec_ref_known(v_p_1393_, 3);
v___x_1432_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1429_, v_v_1430_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v_k_1429_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1438_, lean_object* v_acc_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1438_, v_acc_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
if (lean_obj_tag(v_p_1453_) == 0)
{
lean_object* v_k_1466_; lean_object* v___x_1467_; 
v_k_1466_ = lean_ctor_get(v_p_1453_, 0);
lean_inc(v_k_1466_);
lean_dec_ref_known(v_p_1453_, 1);
v___x_1467_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1466_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
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
lean_dec_ref_known(v_p_1453_, 3);
v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1468_, v_v_1469_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v_k_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1470_, v_a_1472_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
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
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1488_; double v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_float_of_nat(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1546_; 
v_ref_1500_ = lean_ctor_get(v___y_1497_, 5);
v___x_1501_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
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
v___x_1525_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1526_ = 0;
v___x_1527_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1528_, 0, v_cls_1493_);
lean_ctor_set(v___x_1528_, 1, v___x_1524_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
lean_ctor_set_float(v___x_1528_, sizeof(void*)*3, v___x_1525_);
lean_ctor_set_float(v___x_1528_, sizeof(void*)*3 + 8, v___x_1525_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*3 + 16, v___x_1526_);
v___x_1529_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1547_, lean_object* v_msg_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1547_, v_msg_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1554_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1570_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1571_ = l_Lean_Name_append(v___x_1570_, v___x_1569_);
return v___x_1571_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
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
lean_dec_ref_known(v_a_1598_, 1);
lean_inc_ref(v_p_1575_);
v___x_1603_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = l_Lean_Meta_Sym_canon(v_a_1604_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = l_Lean_Meta_Sym_shareCommon(v_a_1606_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
lean_inc_ref(v_p_1575_);
v___x_1609_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_n(v_a_1610_, 2);
lean_dec_ref_known(v___x_1609_, 1);
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
lean_dec_ref_known(v_a_1615_, 1);
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
v___x_1629_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1625_, v___x_1612_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec_ref_known(v___x_1612_, 1);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1630_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc_n(v_a_1632_, 2);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
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
v___x_1652_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1575_, v_a_1639_);
if (v___x_1652_ == 0)
{
lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_del_object(v___x_1636_);
v___f_1653_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1653_, 0, v_a_1588_);
v___x_1654_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1654_, v___f_1653_, v_a_1576_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_options_1656_; uint8_t v_hasTrace_1657_; 
lean_dec_ref_known(v___x_1655_, 1);
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
v___x_1659_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1660_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1658_, v_options_1656_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v_p_1575_);
goto v___jp_1643_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1575_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
lean_inc(v_a_1639_);
v___x_1664_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1639_, v_a_1576_, v_a_1584_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_a_1663_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_a_1665_);
v___x_1669_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1659_, v___x_1668_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_dec_ref_known(v___x_1669_, 1);
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
lean_dec_ref_known(v___x_1612_, 1);
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
lean_dec_ref_known(v___x_1612_, 1);
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
lean_dec_ref_known(v___x_1612_, 1);
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
lean_dec_ref_known(v___x_1612_, 1);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1835_, v_msg_1836_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1850_, v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1865_, lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1866_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1880_, v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
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
