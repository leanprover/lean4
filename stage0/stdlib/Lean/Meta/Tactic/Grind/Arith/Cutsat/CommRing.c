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
lean_object* v_vars_223_; lean_object* v_varMap_224_; lean_object* v_vars_x27_225_; lean_object* v_varMap_x27_226_; lean_object* v_natToIntMap_227_; lean_object* v_natDef_228_; lean_object* v_dvds_229_; lean_object* v_lowers_230_; lean_object* v_uppers_231_; lean_object* v_diseqs_232_; lean_object* v_elimEqs_233_; lean_object* v_elimStack_234_; lean_object* v_occurs_235_; lean_object* v_assignment_236_; lean_object* v_nextCnstrId_237_; uint8_t v_caseSplits_238_; lean_object* v_steps_239_; lean_object* v_conflict_x3f_240_; lean_object* v_diseqSplits_241_; lean_object* v_divMod_242_; lean_object* v_toIntIds_243_; lean_object* v_toIntInfos_244_; lean_object* v_toIntTermMap_245_; lean_object* v_toIntVarMap_246_; lean_object* v_nonlinearOccs_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
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
v_caseSplits_238_ = lean_ctor_get_uint8(v_s_222_, sizeof(void*)*24);
v_steps_239_ = lean_ctor_get(v_s_222_, 15);
v_conflict_x3f_240_ = lean_ctor_get(v_s_222_, 16);
v_diseqSplits_241_ = lean_ctor_get(v_s_222_, 17);
v_divMod_242_ = lean_ctor_get(v_s_222_, 18);
v_toIntIds_243_ = lean_ctor_get(v_s_222_, 19);
v_toIntInfos_244_ = lean_ctor_get(v_s_222_, 20);
v_toIntTermMap_245_ = lean_ctor_get(v_s_222_, 21);
v_toIntVarMap_246_ = lean_ctor_get(v_s_222_, 22);
v_nonlinearOccs_247_ = lean_ctor_get(v_s_222_, 23);
v_isSharedCheck_254_ = !lean_is_exclusive(v_s_222_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v_s_222_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_nonlinearOccs_247_);
lean_inc(v_toIntVarMap_246_);
lean_inc(v_toIntTermMap_245_);
lean_inc(v_toIntInfos_244_);
lean_inc(v_toIntIds_243_);
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
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_vars_223_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_varMap_224_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_vars_x27_225_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_varMap_x27_226_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_natToIntMap_227_);
lean_ctor_set(v_reuseFailAlloc_253_, 5, v_natDef_228_);
lean_ctor_set(v_reuseFailAlloc_253_, 6, v_dvds_229_);
lean_ctor_set(v_reuseFailAlloc_253_, 7, v_lowers_230_);
lean_ctor_set(v_reuseFailAlloc_253_, 8, v_uppers_231_);
lean_ctor_set(v_reuseFailAlloc_253_, 9, v_diseqs_232_);
lean_ctor_set(v_reuseFailAlloc_253_, 10, v_elimEqs_233_);
lean_ctor_set(v_reuseFailAlloc_253_, 11, v_elimStack_234_);
lean_ctor_set(v_reuseFailAlloc_253_, 12, v_occurs_235_);
lean_ctor_set(v_reuseFailAlloc_253_, 13, v_assignment_236_);
lean_ctor_set(v_reuseFailAlloc_253_, 14, v_nextCnstrId_237_);
lean_ctor_set(v_reuseFailAlloc_253_, 15, v_steps_239_);
lean_ctor_set(v_reuseFailAlloc_253_, 16, v_conflict_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 17, v_diseqSplits_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 18, v_divMod_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 19, v_toIntIds_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 20, v_toIntInfos_244_);
lean_ctor_set(v_reuseFailAlloc_253_, 21, v_toIntTermMap_245_);
lean_ctor_set(v_reuseFailAlloc_253_, 22, v_toIntVarMap_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 23, v_nonlinearOccs_247_);
lean_ctor_set_uint8(v_reuseFailAlloc_253_, sizeof(void*)*24, v_caseSplits_238_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*24 + 1, v_a_221_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_255_, lean_object* v_s_256_){
_start:
{
uint8_t v_a_153350__boxed_257_; lean_object* v_res_258_; 
v_a_153350__boxed_257_ = lean_unbox(v_a_255_);
v_res_258_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_153350__boxed_257_, v_s_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_259_, lean_object* v_s_260_){
_start:
{
lean_object* v_toRing_261_; lean_object* v_invFn_x3f_262_; lean_object* v_semiringId_x3f_263_; lean_object* v_commSemiringInst_264_; lean_object* v_commRingInst_265_; lean_object* v_noZeroDivInst_x3f_266_; lean_object* v_fieldInst_x3f_267_; lean_object* v_powIdentityInst_x3f_268_; lean_object* v_denoteEntries_269_; lean_object* v_nextId_270_; lean_object* v_steps_271_; lean_object* v_queue_272_; lean_object* v_basis_273_; lean_object* v_diseqs_274_; uint8_t v_recheck_275_; lean_object* v_invSet_276_; lean_object* v_powIdentityVarCount_277_; lean_object* v_numEq0_x3f_278_; uint8_t v_numEq0Updated_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_311_; 
v_toRing_261_ = lean_ctor_get(v_s_260_, 0);
v_invFn_x3f_262_ = lean_ctor_get(v_s_260_, 1);
v_semiringId_x3f_263_ = lean_ctor_get(v_s_260_, 2);
v_commSemiringInst_264_ = lean_ctor_get(v_s_260_, 3);
v_commRingInst_265_ = lean_ctor_get(v_s_260_, 4);
v_noZeroDivInst_x3f_266_ = lean_ctor_get(v_s_260_, 5);
v_fieldInst_x3f_267_ = lean_ctor_get(v_s_260_, 6);
v_powIdentityInst_x3f_268_ = lean_ctor_get(v_s_260_, 7);
v_denoteEntries_269_ = lean_ctor_get(v_s_260_, 8);
v_nextId_270_ = lean_ctor_get(v_s_260_, 9);
v_steps_271_ = lean_ctor_get(v_s_260_, 10);
v_queue_272_ = lean_ctor_get(v_s_260_, 11);
v_basis_273_ = lean_ctor_get(v_s_260_, 12);
v_diseqs_274_ = lean_ctor_get(v_s_260_, 13);
v_recheck_275_ = lean_ctor_get_uint8(v_s_260_, sizeof(void*)*17);
v_invSet_276_ = lean_ctor_get(v_s_260_, 14);
v_powIdentityVarCount_277_ = lean_ctor_get(v_s_260_, 15);
v_numEq0_x3f_278_ = lean_ctor_get(v_s_260_, 16);
v_numEq0Updated_279_ = lean_ctor_get_uint8(v_s_260_, sizeof(void*)*17 + 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_s_260_);
if (v_isSharedCheck_311_ == 0)
{
v___x_281_ = v_s_260_;
v_isShared_282_ = v_isSharedCheck_311_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_numEq0_x3f_278_);
lean_inc(v_powIdentityVarCount_277_);
lean_inc(v_invSet_276_);
lean_inc(v_diseqs_274_);
lean_inc(v_basis_273_);
lean_inc(v_queue_272_);
lean_inc(v_steps_271_);
lean_inc(v_nextId_270_);
lean_inc(v_denoteEntries_269_);
lean_inc(v_powIdentityInst_x3f_268_);
lean_inc(v_fieldInst_x3f_267_);
lean_inc(v_noZeroDivInst_x3f_266_);
lean_inc(v_commRingInst_265_);
lean_inc(v_commSemiringInst_264_);
lean_inc(v_semiringId_x3f_263_);
lean_inc(v_invFn_x3f_262_);
lean_inc(v_toRing_261_);
lean_dec(v_s_260_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_311_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_id_283_; lean_object* v_type_284_; lean_object* v_u_285_; lean_object* v_ringInst_286_; lean_object* v_semiringInst_287_; lean_object* v_charInst_x3f_288_; lean_object* v_addFn_x3f_289_; lean_object* v_mulFn_x3f_290_; lean_object* v_subFn_x3f_291_; lean_object* v_powFn_x3f_292_; lean_object* v_intCastFn_x3f_293_; lean_object* v_natCastFn_x3f_294_; lean_object* v_one_x3f_295_; lean_object* v_vars_296_; lean_object* v_varMap_297_; lean_object* v_denote_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_309_; 
v_id_283_ = lean_ctor_get(v_toRing_261_, 0);
v_type_284_ = lean_ctor_get(v_toRing_261_, 1);
v_u_285_ = lean_ctor_get(v_toRing_261_, 2);
v_ringInst_286_ = lean_ctor_get(v_toRing_261_, 3);
v_semiringInst_287_ = lean_ctor_get(v_toRing_261_, 4);
v_charInst_x3f_288_ = lean_ctor_get(v_toRing_261_, 5);
v_addFn_x3f_289_ = lean_ctor_get(v_toRing_261_, 6);
v_mulFn_x3f_290_ = lean_ctor_get(v_toRing_261_, 7);
v_subFn_x3f_291_ = lean_ctor_get(v_toRing_261_, 8);
v_powFn_x3f_292_ = lean_ctor_get(v_toRing_261_, 10);
v_intCastFn_x3f_293_ = lean_ctor_get(v_toRing_261_, 11);
v_natCastFn_x3f_294_ = lean_ctor_get(v_toRing_261_, 12);
v_one_x3f_295_ = lean_ctor_get(v_toRing_261_, 13);
v_vars_296_ = lean_ctor_get(v_toRing_261_, 14);
v_varMap_297_ = lean_ctor_get(v_toRing_261_, 15);
v_denote_298_ = lean_ctor_get(v_toRing_261_, 16);
v_isSharedCheck_309_ = !lean_is_exclusive(v_toRing_261_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v_toRing_261_, 9);
lean_dec(v_unused_310_);
v___x_300_ = v_toRing_261_;
v_isShared_301_ = v_isSharedCheck_309_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_denote_298_);
lean_inc(v_varMap_297_);
lean_inc(v_vars_296_);
lean_inc(v_one_x3f_295_);
lean_inc(v_natCastFn_x3f_294_);
lean_inc(v_intCastFn_x3f_293_);
lean_inc(v_powFn_x3f_292_);
lean_inc(v_subFn_x3f_291_);
lean_inc(v_mulFn_x3f_290_);
lean_inc(v_addFn_x3f_289_);
lean_inc(v_charInst_x3f_288_);
lean_inc(v_semiringInst_287_);
lean_inc(v_ringInst_286_);
lean_inc(v_u_285_);
lean_inc(v_type_284_);
lean_inc(v_id_283_);
lean_dec(v_toRing_261_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_309_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_a_259_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 9, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_id_283_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_type_284_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_u_285_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_ringInst_286_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_semiringInst_287_);
lean_ctor_set(v_reuseFailAlloc_308_, 5, v_charInst_x3f_288_);
lean_ctor_set(v_reuseFailAlloc_308_, 6, v_addFn_x3f_289_);
lean_ctor_set(v_reuseFailAlloc_308_, 7, v_mulFn_x3f_290_);
lean_ctor_set(v_reuseFailAlloc_308_, 8, v_subFn_x3f_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 9, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 10, v_powFn_x3f_292_);
lean_ctor_set(v_reuseFailAlloc_308_, 11, v_intCastFn_x3f_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 12, v_natCastFn_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_308_, 13, v_one_x3f_295_);
lean_ctor_set(v_reuseFailAlloc_308_, 14, v_vars_296_);
lean_ctor_set(v_reuseFailAlloc_308_, 15, v_varMap_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 16, v_denote_298_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_304_);
v___x_306_ = v___x_281_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_invFn_x3f_262_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_semiringId_x3f_263_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_commSemiringInst_264_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_commRingInst_265_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_noZeroDivInst_x3f_266_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_fieldInst_x3f_267_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_powIdentityInst_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_denoteEntries_269_);
lean_ctor_set(v_reuseFailAlloc_307_, 9, v_nextId_270_);
lean_ctor_set(v_reuseFailAlloc_307_, 10, v_steps_271_);
lean_ctor_set(v_reuseFailAlloc_307_, 11, v_queue_272_);
lean_ctor_set(v_reuseFailAlloc_307_, 12, v_basis_273_);
lean_ctor_set(v_reuseFailAlloc_307_, 13, v_diseqs_274_);
lean_ctor_set(v_reuseFailAlloc_307_, 14, v_invSet_276_);
lean_ctor_set(v_reuseFailAlloc_307_, 15, v_powIdentityVarCount_277_);
lean_ctor_set(v_reuseFailAlloc_307_, 16, v_numEq0_x3f_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*17, v_recheck_275_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*17 + 1, v_numEq0Updated_279_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; lean_object* v_env_319_; lean_object* v___x_320_; lean_object* v_mctx_321_; lean_object* v_lctx_322_; lean_object* v_options_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_318_ = lean_st_ref_get(v___y_316_);
v_env_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc_ref(v_env_319_);
lean_dec(v___x_318_);
v___x_320_ = lean_st_ref_get(v___y_314_);
v_mctx_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_ref(v_mctx_321_);
lean_dec(v___x_320_);
v_lctx_322_ = lean_ctor_get(v___y_313_, 2);
v_options_323_ = lean_ctor_get(v___y_315_, 2);
lean_inc_ref(v_options_323_);
lean_inc_ref(v_lctx_322_);
v___x_324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_324_, 0, v_env_319_);
lean_ctor_set(v___x_324_, 1, v_mctx_321_);
lean_ctor_set(v___x_324_, 2, v_lctx_322_);
lean_ctor_set(v___x_324_, 3, v_options_323_);
v___x_325_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_msgData_312_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_ref_340_; lean_object* v___x_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_350_; 
v_ref_340_ = lean_ctor_get(v___y_337_, 5);
v___x_341_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_350_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_inc(v_ref_340_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_ref_340_);
lean_ctor_set(v___x_346_, 1, v_a_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 1);
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_348_ = v___x_344_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_357_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
lean_inc_ref(v_type_361_);
v___x_374_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_361_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
if (lean_obj_tag(v_a_375_) == 1)
{
lean_object* v_val_379_; lean_object* v___x_381_; 
lean_dec_ref(v_type_361_);
v_val_379_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v_a_375_, 1);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v_val_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_val_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_del_object(v___x_377_);
lean_dec(v_a_375_);
v___x_383_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_384_ = l_Lean_indentExpr(v_type_361_);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_385_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_386_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_type_361_);
v_a_388_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_374_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_374_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_410_, lean_object* v_u_411_, lean_object* v_instDeclName_412_, lean_object* v_declName_413_, lean_object* v_expectedInst_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v_u_411_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
lean_inc_ref(v___x_428_);
v___x_429_ = l_Lean_mkConst(v_instDeclName_412_, v___x_428_);
lean_inc_ref(v_type_410_);
v___x_430_ = l_Lean_Expr_app___override(v___x_429_, v_type_410_);
v___x_431_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_430_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_n(v_a_432_, 2);
lean_dec_ref_known(v___x_431_, 1);
lean_inc(v_declName_413_);
v___x_433_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_413_, v_a_432_, v_expectedInst_414_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref_known(v___x_433_, 1);
v___x_434_ = l_Lean_mkConst(v_declName_413_, v___x_428_);
v___x_435_ = l_Lean_mkAppB(v___x_434_, v_type_410_, v_a_432_);
v___x_436_ = l_Lean_Meta_Sym_canon(v___x_435_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = l_Lean_Meta_Sym_shareCommon(v_a_437_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_438_;
}
else
{
return v___x_436_;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_432_);
lean_dec_ref_known(v___x_428_, 2);
lean_dec(v_declName_413_);
lean_dec_ref(v_type_410_);
v_a_439_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_433_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_428_, 2);
lean_dec_ref(v_expectedInst_414_);
lean_dec(v_declName_413_);
lean_dec_ref(v_type_410_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_447_ = _args[0];
lean_object* v_u_448_ = _args[1];
lean_object* v_instDeclName_449_ = _args[2];
lean_object* v_declName_450_ = _args[3];
lean_object* v_expectedInst_451_ = _args[4];
lean_object* v___y_452_ = _args[5];
lean_object* v___y_453_ = _args[6];
lean_object* v___y_454_ = _args[7];
lean_object* v___y_455_ = _args[8];
lean_object* v___y_456_ = _args[9];
lean_object* v___y_457_ = _args[10];
lean_object* v___y_458_ = _args[11];
lean_object* v___y_459_ = _args[12];
lean_object* v___y_460_ = _args[13];
lean_object* v___y_461_ = _args[14];
lean_object* v___y_462_ = _args[15];
lean_object* v___y_463_ = _args[16];
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_447_, v_u_448_, v_instDeclName_449_, v_declName_450_, v_expectedInst_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_534_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_534_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_534_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_534_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_toRing_498_; lean_object* v_negFn_x3f_499_; 
v_toRing_498_ = lean_ctor_get(v_a_494_, 0);
lean_inc_ref(v_toRing_498_);
lean_dec(v_a_494_);
v_negFn_x3f_499_ = lean_ctor_get(v_toRing_498_, 9);
if (lean_obj_tag(v_negFn_x3f_499_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; 
lean_inc_ref(v_negFn_x3f_499_);
lean_dec_ref(v_toRing_498_);
v_val_500_ = lean_ctor_get(v_negFn_x3f_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_negFn_x3f_499_, 1);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_val_500_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_val_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
else
{
lean_object* v_type_504_; lean_object* v_u_505_; lean_object* v_ringInst_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_expectedInst_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_496_);
v_type_504_ = lean_ctor_get(v_toRing_498_, 1);
lean_inc_ref_n(v_type_504_, 2);
v_u_505_ = lean_ctor_get(v_toRing_498_, 2);
lean_inc_n(v_u_505_, 2);
v_ringInst_506_ = lean_ctor_get(v_toRing_498_, 3);
lean_inc_ref(v_ringInst_506_);
lean_dec_ref(v_toRing_498_);
v___x_507_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v_u_505_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_mkConst(v___x_507_, v___x_509_);
v_expectedInst_511_ = l_Lean_mkAppB(v___x_510_, v_type_504_, v_ringInst_506_);
v___x_512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_513_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8));
v___x_514_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_504_, v_u_505_, v___x_512_, v___x_513_, v_expectedInst_511_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_n(v_a_515_, 2);
lean_dec_ref_known(v___x_514_, 1);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_516_, 0, v_a_515_);
v___x_517_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_516_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_525_);
v___x_519_ = v___x_517_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_dec(v___x_517_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_a_515_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_515_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_515_);
v_a_526_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_517_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_517_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_493_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_493_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_to_int(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v_toRing_586_; lean_object* v_type_587_; lean_object* v_u_588_; lean_object* v_semiringInst_589_; lean_object* v___x_590_; lean_object* v_n_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v_toRing_586_ = lean_ctor_get(v_a_585_, 0);
lean_inc_ref(v_toRing_586_);
lean_dec(v_a_585_);
v_type_587_ = lean_ctor_get(v_toRing_586_, 1);
lean_inc_ref_n(v_type_587_, 2);
v_u_588_ = lean_ctor_get(v_toRing_586_, 2);
lean_inc(v_u_588_);
v_semiringInst_589_ = lean_ctor_get(v_toRing_586_, 4);
lean_inc_ref(v_semiringInst_589_);
lean_dec_ref(v_toRing_586_);
v___x_590_ = lean_nat_abs(v_k_571_);
v_n_591_ = l_Lean_mkRawNatLit(v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v_u_588_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
lean_inc_ref(v___x_594_);
v___x_595_ = l_Lean_mkConst(v___x_592_, v___x_594_);
lean_inc_ref(v_n_591_);
v___x_596_ = l_Lean_mkAppB(v___x_595_, v_type_587_, v_n_591_);
v___x_597_ = lean_box(0);
v___x_598_ = l_Lean_Meta_synthInstance_x3f(v___x_596_, v___x_597_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_638_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_638_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_638_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_638_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_ofNatInst_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; 
if (lean_obj_tag(v_a_599_) == 1)
{
lean_object* v_val_634_; 
lean_dec_ref(v_semiringInst_589_);
v_val_634_ = lean_ctor_get(v_a_599_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_a_599_, 1);
v_ofNatInst_604_ = v_val_634_;
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
v___y_615_ = v___y_582_;
goto v___jp_603_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_a_599_);
v___x_635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6));
lean_inc_ref(v___x_594_);
v___x_636_ = l_Lean_mkConst(v___x_635_, v___x_594_);
lean_inc_ref(v_n_591_);
lean_inc_ref(v_type_587_);
v___x_637_ = l_Lean_mkApp3(v___x_636_, v_type_587_, v_semiringInst_589_, v_n_591_);
v_ofNatInst_604_ = v___x_637_;
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
v___y_615_ = v___y_582_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_n_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_616_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_617_ = l_Lean_mkConst(v___x_616_, v___x_594_);
v_n_618_ = l_Lean_mkApp3(v___x_617_, v_type_587_, v_n_591_, v_ofNatInst_604_);
v___x_619_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_620_ = lean_int_dec_lt(v_k_571_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_622_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_n_618_);
v___x_622_ = v___x_601_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_n_618_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v___x_624_; 
lean_del_object(v___x_601_);
v___x_624_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_Expr_app___override(v_a_625_, v_n_618_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_dec_ref(v_n_618_);
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref_known(v___x_594_, 2);
lean_dec_ref(v_n_591_);
lean_dec_ref(v_semiringInst_589_);
lean_dec_ref(v_type_587_);
v_a_639_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_598_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_598_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_584_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_584_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v_k_655_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_669_, lean_object* v_u_670_, lean_object* v_instDeclName_671_, lean_object* v_declName_672_, lean_object* v_expectedInst_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_686_ = lean_box(0);
lean_inc_n(v_u_670_, 2);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v_u_670_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_u_670_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_689_, 0, v_u_670_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_inc_ref(v___x_689_);
v___x_690_ = l_Lean_mkConst(v_instDeclName_671_, v___x_689_);
lean_inc_ref_n(v_type_669_, 3);
v___x_691_ = l_Lean_mkApp3(v___x_690_, v_type_669_, v_type_669_, v_type_669_);
v___x_692_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_691_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_n(v_a_693_, 2);
lean_dec_ref_known(v___x_692_, 1);
lean_inc(v_declName_672_);
v___x_694_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_672_, v_a_693_, v_expectedInst_673_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref_known(v___x_694_, 1);
v___x_695_ = l_Lean_mkConst(v_declName_672_, v___x_689_);
lean_inc_ref_n(v_type_669_, 2);
v___x_696_ = l_Lean_mkApp4(v___x_695_, v_type_669_, v_type_669_, v_type_669_, v_a_693_);
v___x_697_ = l_Lean_Meta_Sym_canon(v___x_696_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l_Lean_Meta_Sym_shareCommon(v_a_698_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_699_;
}
else
{
return v___x_697_;
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_a_693_);
lean_dec_ref_known(v___x_689_, 2);
lean_dec(v_declName_672_);
lean_dec_ref(v_type_669_);
v_a_700_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_694_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_694_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_689_, 2);
lean_dec_ref(v_expectedInst_673_);
lean_dec(v_declName_672_);
lean_dec_ref(v_type_669_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_708_ = _args[0];
lean_object* v_u_709_ = _args[1];
lean_object* v_instDeclName_710_ = _args[2];
lean_object* v_declName_711_ = _args[3];
lean_object* v_expectedInst_712_ = _args[4];
lean_object* v___y_713_ = _args[5];
lean_object* v___y_714_ = _args[6];
lean_object* v___y_715_ = _args[7];
lean_object* v___y_716_ = _args[8];
lean_object* v___y_717_ = _args[9];
lean_object* v___y_718_ = _args[10];
lean_object* v___y_719_ = _args[11];
lean_object* v___y_720_ = _args[12];
lean_object* v___y_721_ = _args[13];
lean_object* v___y_722_ = _args[14];
lean_object* v___y_723_ = _args[15];
lean_object* v___y_724_ = _args[16];
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_708_, v_u_709_, v_instDeclName_710_, v_declName_711_, v_expectedInst_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_726_, lean_object* v_s_727_){
_start:
{
lean_object* v_toRing_728_; lean_object* v_invFn_x3f_729_; lean_object* v_semiringId_x3f_730_; lean_object* v_commSemiringInst_731_; lean_object* v_commRingInst_732_; lean_object* v_noZeroDivInst_x3f_733_; lean_object* v_fieldInst_x3f_734_; lean_object* v_powIdentityInst_x3f_735_; lean_object* v_denoteEntries_736_; lean_object* v_nextId_737_; lean_object* v_steps_738_; lean_object* v_queue_739_; lean_object* v_basis_740_; lean_object* v_diseqs_741_; uint8_t v_recheck_742_; lean_object* v_invSet_743_; lean_object* v_powIdentityVarCount_744_; lean_object* v_numEq0_x3f_745_; uint8_t v_numEq0Updated_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_778_; 
v_toRing_728_ = lean_ctor_get(v_s_727_, 0);
v_invFn_x3f_729_ = lean_ctor_get(v_s_727_, 1);
v_semiringId_x3f_730_ = lean_ctor_get(v_s_727_, 2);
v_commSemiringInst_731_ = lean_ctor_get(v_s_727_, 3);
v_commRingInst_732_ = lean_ctor_get(v_s_727_, 4);
v_noZeroDivInst_x3f_733_ = lean_ctor_get(v_s_727_, 5);
v_fieldInst_x3f_734_ = lean_ctor_get(v_s_727_, 6);
v_powIdentityInst_x3f_735_ = lean_ctor_get(v_s_727_, 7);
v_denoteEntries_736_ = lean_ctor_get(v_s_727_, 8);
v_nextId_737_ = lean_ctor_get(v_s_727_, 9);
v_steps_738_ = lean_ctor_get(v_s_727_, 10);
v_queue_739_ = lean_ctor_get(v_s_727_, 11);
v_basis_740_ = lean_ctor_get(v_s_727_, 12);
v_diseqs_741_ = lean_ctor_get(v_s_727_, 13);
v_recheck_742_ = lean_ctor_get_uint8(v_s_727_, sizeof(void*)*17);
v_invSet_743_ = lean_ctor_get(v_s_727_, 14);
v_powIdentityVarCount_744_ = lean_ctor_get(v_s_727_, 15);
v_numEq0_x3f_745_ = lean_ctor_get(v_s_727_, 16);
v_numEq0Updated_746_ = lean_ctor_get_uint8(v_s_727_, sizeof(void*)*17 + 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_s_727_);
if (v_isSharedCheck_778_ == 0)
{
v___x_748_ = v_s_727_;
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_numEq0_x3f_745_);
lean_inc(v_powIdentityVarCount_744_);
lean_inc(v_invSet_743_);
lean_inc(v_diseqs_741_);
lean_inc(v_basis_740_);
lean_inc(v_queue_739_);
lean_inc(v_steps_738_);
lean_inc(v_nextId_737_);
lean_inc(v_denoteEntries_736_);
lean_inc(v_powIdentityInst_x3f_735_);
lean_inc(v_fieldInst_x3f_734_);
lean_inc(v_noZeroDivInst_x3f_733_);
lean_inc(v_commRingInst_732_);
lean_inc(v_commSemiringInst_731_);
lean_inc(v_semiringId_x3f_730_);
lean_inc(v_invFn_x3f_729_);
lean_inc(v_toRing_728_);
lean_dec(v_s_727_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_id_750_; lean_object* v_type_751_; lean_object* v_u_752_; lean_object* v_ringInst_753_; lean_object* v_semiringInst_754_; lean_object* v_charInst_x3f_755_; lean_object* v_addFn_x3f_756_; lean_object* v_subFn_x3f_757_; lean_object* v_negFn_x3f_758_; lean_object* v_powFn_x3f_759_; lean_object* v_intCastFn_x3f_760_; lean_object* v_natCastFn_x3f_761_; lean_object* v_one_x3f_762_; lean_object* v_vars_763_; lean_object* v_varMap_764_; lean_object* v_denote_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_776_; 
v_id_750_ = lean_ctor_get(v_toRing_728_, 0);
v_type_751_ = lean_ctor_get(v_toRing_728_, 1);
v_u_752_ = lean_ctor_get(v_toRing_728_, 2);
v_ringInst_753_ = lean_ctor_get(v_toRing_728_, 3);
v_semiringInst_754_ = lean_ctor_get(v_toRing_728_, 4);
v_charInst_x3f_755_ = lean_ctor_get(v_toRing_728_, 5);
v_addFn_x3f_756_ = lean_ctor_get(v_toRing_728_, 6);
v_subFn_x3f_757_ = lean_ctor_get(v_toRing_728_, 8);
v_negFn_x3f_758_ = lean_ctor_get(v_toRing_728_, 9);
v_powFn_x3f_759_ = lean_ctor_get(v_toRing_728_, 10);
v_intCastFn_x3f_760_ = lean_ctor_get(v_toRing_728_, 11);
v_natCastFn_x3f_761_ = lean_ctor_get(v_toRing_728_, 12);
v_one_x3f_762_ = lean_ctor_get(v_toRing_728_, 13);
v_vars_763_ = lean_ctor_get(v_toRing_728_, 14);
v_varMap_764_ = lean_ctor_get(v_toRing_728_, 15);
v_denote_765_ = lean_ctor_get(v_toRing_728_, 16);
v_isSharedCheck_776_ = !lean_is_exclusive(v_toRing_728_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_toRing_728_, 7);
lean_dec(v_unused_777_);
v___x_767_ = v_toRing_728_;
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_denote_765_);
lean_inc(v_varMap_764_);
lean_inc(v_vars_763_);
lean_inc(v_one_x3f_762_);
lean_inc(v_natCastFn_x3f_761_);
lean_inc(v_intCastFn_x3f_760_);
lean_inc(v_powFn_x3f_759_);
lean_inc(v_negFn_x3f_758_);
lean_inc(v_subFn_x3f_757_);
lean_inc(v_addFn_x3f_756_);
lean_inc(v_charInst_x3f_755_);
lean_inc(v_semiringInst_754_);
lean_inc(v_ringInst_753_);
lean_inc(v_u_752_);
lean_inc(v_type_751_);
lean_inc(v_id_750_);
lean_dec(v_toRing_728_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_726_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 7, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_id_750_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_type_751_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_u_752_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_ringInst_753_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_semiringInst_754_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_charInst_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_addFn_x3f_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_subFn_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_775_, 9, v_negFn_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 10, v_powFn_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 11, v_intCastFn_x3f_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 12, v_natCastFn_x3f_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 13, v_one_x3f_762_);
lean_ctor_set(v_reuseFailAlloc_775_, 14, v_vars_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 15, v_varMap_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 16, v_denote_765_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_771_);
v___x_773_ = v___x_748_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_invFn_x3f_729_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_semiringId_x3f_730_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_commSemiringInst_731_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_commRingInst_732_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_noZeroDivInst_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_fieldInst_x3f_734_);
lean_ctor_set(v_reuseFailAlloc_774_, 7, v_powIdentityInst_x3f_735_);
lean_ctor_set(v_reuseFailAlloc_774_, 8, v_denoteEntries_736_);
lean_ctor_set(v_reuseFailAlloc_774_, 9, v_nextId_737_);
lean_ctor_set(v_reuseFailAlloc_774_, 10, v_steps_738_);
lean_ctor_set(v_reuseFailAlloc_774_, 11, v_queue_739_);
lean_ctor_set(v_reuseFailAlloc_774_, 12, v_basis_740_);
lean_ctor_set(v_reuseFailAlloc_774_, 13, v_diseqs_741_);
lean_ctor_set(v_reuseFailAlloc_774_, 14, v_invSet_743_);
lean_ctor_set(v_reuseFailAlloc_774_, 15, v_powIdentityVarCount_744_);
lean_ctor_set(v_reuseFailAlloc_774_, 16, v_numEq0_x3f_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*17, v_recheck_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*17 + 1, v_numEq0Updated_746_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_846_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_846_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_846_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_846_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_toRing_807_; lean_object* v_mulFn_x3f_808_; 
v_toRing_807_ = lean_ctor_get(v_a_803_, 0);
lean_inc_ref(v_toRing_807_);
lean_dec(v_a_803_);
v_mulFn_x3f_808_ = lean_ctor_get(v_toRing_807_, 7);
if (lean_obj_tag(v_mulFn_x3f_808_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_811_; 
lean_inc_ref(v_mulFn_x3f_808_);
lean_dec_ref(v_toRing_807_);
v_val_809_ = lean_ctor_get(v_mulFn_x3f_808_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_mulFn_x3f_808_, 1);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_val_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_type_813_; lean_object* v_u_814_; lean_object* v_semiringInst_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_expectedInst_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_del_object(v___x_805_);
v_type_813_ = lean_ctor_get(v_toRing_807_, 1);
lean_inc_ref_n(v_type_813_, 3);
v_u_814_ = lean_ctor_get(v_toRing_807_, 2);
lean_inc_n(v_u_814_, 2);
v_semiringInst_815_ = lean_ctor_get(v_toRing_807_, 4);
lean_inc_ref(v_semiringInst_815_);
lean_dec_ref(v_toRing_807_);
v___x_816_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v_u_814_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_inc_ref(v___x_818_);
v___x_819_ = l_Lean_mkConst(v___x_816_, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_821_ = l_Lean_mkConst(v___x_820_, v___x_818_);
v___x_822_ = l_Lean_mkAppB(v___x_821_, v_type_813_, v_semiringInst_815_);
v_expectedInst_823_ = l_Lean_mkAppB(v___x_819_, v_type_813_, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_825_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_826_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_813_, v_u_814_, v___x_824_, v___x_825_, v_expectedInst_823_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___f_828_; lean_object* v___x_829_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_n(v_a_827_, 2);
lean_dec_ref_known(v___x_826_, 1);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_828_, 0, v_a_827_);
v___x_829_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_828_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_837_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_a_827_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_827_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_a_827_);
v_a_838_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_829_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_829_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_802_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_802_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_868_, lean_object* v_s_869_){
_start:
{
lean_object* v_toRing_870_; lean_object* v_invFn_x3f_871_; lean_object* v_semiringId_x3f_872_; lean_object* v_commSemiringInst_873_; lean_object* v_commRingInst_874_; lean_object* v_noZeroDivInst_x3f_875_; lean_object* v_fieldInst_x3f_876_; lean_object* v_powIdentityInst_x3f_877_; lean_object* v_denoteEntries_878_; lean_object* v_nextId_879_; lean_object* v_steps_880_; lean_object* v_queue_881_; lean_object* v_basis_882_; lean_object* v_diseqs_883_; uint8_t v_recheck_884_; lean_object* v_invSet_885_; lean_object* v_powIdentityVarCount_886_; lean_object* v_numEq0_x3f_887_; uint8_t v_numEq0Updated_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_920_; 
v_toRing_870_ = lean_ctor_get(v_s_869_, 0);
v_invFn_x3f_871_ = lean_ctor_get(v_s_869_, 1);
v_semiringId_x3f_872_ = lean_ctor_get(v_s_869_, 2);
v_commSemiringInst_873_ = lean_ctor_get(v_s_869_, 3);
v_commRingInst_874_ = lean_ctor_get(v_s_869_, 4);
v_noZeroDivInst_x3f_875_ = lean_ctor_get(v_s_869_, 5);
v_fieldInst_x3f_876_ = lean_ctor_get(v_s_869_, 6);
v_powIdentityInst_x3f_877_ = lean_ctor_get(v_s_869_, 7);
v_denoteEntries_878_ = lean_ctor_get(v_s_869_, 8);
v_nextId_879_ = lean_ctor_get(v_s_869_, 9);
v_steps_880_ = lean_ctor_get(v_s_869_, 10);
v_queue_881_ = lean_ctor_get(v_s_869_, 11);
v_basis_882_ = lean_ctor_get(v_s_869_, 12);
v_diseqs_883_ = lean_ctor_get(v_s_869_, 13);
v_recheck_884_ = lean_ctor_get_uint8(v_s_869_, sizeof(void*)*17);
v_invSet_885_ = lean_ctor_get(v_s_869_, 14);
v_powIdentityVarCount_886_ = lean_ctor_get(v_s_869_, 15);
v_numEq0_x3f_887_ = lean_ctor_get(v_s_869_, 16);
v_numEq0Updated_888_ = lean_ctor_get_uint8(v_s_869_, sizeof(void*)*17 + 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_s_869_);
if (v_isSharedCheck_920_ == 0)
{
v___x_890_ = v_s_869_;
v_isShared_891_ = v_isSharedCheck_920_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_numEq0_x3f_887_);
lean_inc(v_powIdentityVarCount_886_);
lean_inc(v_invSet_885_);
lean_inc(v_diseqs_883_);
lean_inc(v_basis_882_);
lean_inc(v_queue_881_);
lean_inc(v_steps_880_);
lean_inc(v_nextId_879_);
lean_inc(v_denoteEntries_878_);
lean_inc(v_powIdentityInst_x3f_877_);
lean_inc(v_fieldInst_x3f_876_);
lean_inc(v_noZeroDivInst_x3f_875_);
lean_inc(v_commRingInst_874_);
lean_inc(v_commSemiringInst_873_);
lean_inc(v_semiringId_x3f_872_);
lean_inc(v_invFn_x3f_871_);
lean_inc(v_toRing_870_);
lean_dec(v_s_869_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_920_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_id_892_; lean_object* v_type_893_; lean_object* v_u_894_; lean_object* v_ringInst_895_; lean_object* v_semiringInst_896_; lean_object* v_charInst_x3f_897_; lean_object* v_addFn_x3f_898_; lean_object* v_mulFn_x3f_899_; lean_object* v_subFn_x3f_900_; lean_object* v_negFn_x3f_901_; lean_object* v_intCastFn_x3f_902_; lean_object* v_natCastFn_x3f_903_; lean_object* v_one_x3f_904_; lean_object* v_vars_905_; lean_object* v_varMap_906_; lean_object* v_denote_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_918_; 
v_id_892_ = lean_ctor_get(v_toRing_870_, 0);
v_type_893_ = lean_ctor_get(v_toRing_870_, 1);
v_u_894_ = lean_ctor_get(v_toRing_870_, 2);
v_ringInst_895_ = lean_ctor_get(v_toRing_870_, 3);
v_semiringInst_896_ = lean_ctor_get(v_toRing_870_, 4);
v_charInst_x3f_897_ = lean_ctor_get(v_toRing_870_, 5);
v_addFn_x3f_898_ = lean_ctor_get(v_toRing_870_, 6);
v_mulFn_x3f_899_ = lean_ctor_get(v_toRing_870_, 7);
v_subFn_x3f_900_ = lean_ctor_get(v_toRing_870_, 8);
v_negFn_x3f_901_ = lean_ctor_get(v_toRing_870_, 9);
v_intCastFn_x3f_902_ = lean_ctor_get(v_toRing_870_, 11);
v_natCastFn_x3f_903_ = lean_ctor_get(v_toRing_870_, 12);
v_one_x3f_904_ = lean_ctor_get(v_toRing_870_, 13);
v_vars_905_ = lean_ctor_get(v_toRing_870_, 14);
v_varMap_906_ = lean_ctor_get(v_toRing_870_, 15);
v_denote_907_ = lean_ctor_get(v_toRing_870_, 16);
v_isSharedCheck_918_ = !lean_is_exclusive(v_toRing_870_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_toRing_870_, 10);
lean_dec(v_unused_919_);
v___x_909_ = v_toRing_870_;
v_isShared_910_ = v_isSharedCheck_918_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_denote_907_);
lean_inc(v_varMap_906_);
lean_inc(v_vars_905_);
lean_inc(v_one_x3f_904_);
lean_inc(v_natCastFn_x3f_903_);
lean_inc(v_intCastFn_x3f_902_);
lean_inc(v_negFn_x3f_901_);
lean_inc(v_subFn_x3f_900_);
lean_inc(v_mulFn_x3f_899_);
lean_inc(v_addFn_x3f_898_);
lean_inc(v_charInst_x3f_897_);
lean_inc(v_semiringInst_896_);
lean_inc(v_ringInst_895_);
lean_inc(v_u_894_);
lean_inc(v_type_893_);
lean_inc(v_id_892_);
lean_dec(v_toRing_870_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_918_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_a_868_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 10, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_id_892_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_type_893_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_u_894_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_ringInst_895_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_semiringInst_896_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_charInst_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_917_, 6, v_addFn_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_917_, 7, v_mulFn_x3f_899_);
lean_ctor_set(v_reuseFailAlloc_917_, 8, v_subFn_x3f_900_);
lean_ctor_set(v_reuseFailAlloc_917_, 9, v_negFn_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_917_, 10, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_917_, 11, v_intCastFn_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_917_, 12, v_natCastFn_x3f_903_);
lean_ctor_set(v_reuseFailAlloc_917_, 13, v_one_x3f_904_);
lean_ctor_set(v_reuseFailAlloc_917_, 14, v_vars_905_);
lean_ctor_set(v_reuseFailAlloc_917_, 15, v_varMap_906_);
lean_ctor_set(v_reuseFailAlloc_917_, 16, v_denote_907_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_913_);
v___x_915_ = v___x_890_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_invFn_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_semiringId_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_commSemiringInst_873_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_commRingInst_874_);
lean_ctor_set(v_reuseFailAlloc_916_, 5, v_noZeroDivInst_x3f_875_);
lean_ctor_set(v_reuseFailAlloc_916_, 6, v_fieldInst_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_916_, 7, v_powIdentityInst_x3f_877_);
lean_ctor_set(v_reuseFailAlloc_916_, 8, v_denoteEntries_878_);
lean_ctor_set(v_reuseFailAlloc_916_, 9, v_nextId_879_);
lean_ctor_set(v_reuseFailAlloc_916_, 10, v_steps_880_);
lean_ctor_set(v_reuseFailAlloc_916_, 11, v_queue_881_);
lean_ctor_set(v_reuseFailAlloc_916_, 12, v_basis_882_);
lean_ctor_set(v_reuseFailAlloc_916_, 13, v_diseqs_883_);
lean_ctor_set(v_reuseFailAlloc_916_, 14, v_invSet_885_);
lean_ctor_set(v_reuseFailAlloc_916_, 15, v_powIdentityVarCount_886_);
lean_ctor_set(v_reuseFailAlloc_916_, 16, v_numEq0_x3f_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*17, v_recheck_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*17 + 1, v_numEq0Updated_888_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = l_Lean_Level_ofNat(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_931_, lean_object* v_type_932_, lean_object* v_semiringInst_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_947_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_948_ = lean_box(0);
lean_inc(v_u_931_);
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v_u_931_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
lean_inc_ref(v___x_949_);
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_947_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_951_, 0, v_u_931_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
lean_inc_ref(v___x_951_);
v___x_952_ = l_Lean_mkConst(v___x_946_, v___x_951_);
v___x_953_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_932_, 2);
v___x_954_ = l_Lean_mkApp3(v___x_952_, v_type_932_, v___x_953_, v_type_932_);
v___x_955_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_954_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_inst_x27_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc_n(v_a_956_, 2);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_958_ = l_Lean_mkConst(v___x_957_, v___x_949_);
lean_inc_ref(v_type_932_);
v_inst_x27_959_ = l_Lean_mkAppB(v___x_958_, v_type_932_, v_semiringInst_933_);
v___x_960_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_961_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_960_, v_a_956_, v_inst_x27_959_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref_known(v___x_961_, 1);
v___x_962_ = l_Lean_mkConst(v___x_960_, v___x_951_);
lean_inc_ref(v_type_932_);
v___x_963_ = l_Lean_mkApp4(v___x_962_, v_type_932_, v___x_953_, v_type_932_, v_a_956_);
v___x_964_ = l_Lean_Meta_Sym_canon(v___x_963_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = l_Lean_Meta_Sym_shareCommon(v_a_965_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_966_;
}
else
{
return v___x_964_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_a_956_);
lean_dec_ref_known(v___x_951_, 2);
lean_dec_ref(v_type_932_);
v_a_967_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_961_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_961_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_951_, 2);
lean_dec_ref_known(v___x_949_, 2);
lean_dec_ref(v_semiringInst_933_);
lean_dec_ref(v_type_932_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_975_, lean_object* v_type_976_, lean_object* v_semiringInst_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_975_, v_type_976_, v_semiringInst_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1037_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1037_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1037_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_toRing_1008_; lean_object* v_powFn_x3f_1009_; 
v_toRing_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc_ref(v_toRing_1008_);
lean_dec(v_a_1004_);
v_powFn_x3f_1009_ = lean_ctor_get(v_toRing_1008_, 10);
if (lean_obj_tag(v_powFn_x3f_1009_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1012_; 
lean_inc_ref(v_powFn_x3f_1009_);
lean_dec_ref(v_toRing_1008_);
v_val_1010_ = lean_ctor_get(v_powFn_x3f_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_powFn_x3f_1009_, 1);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_val_1010_);
v___x_1012_ = v___x_1006_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v_type_1014_; lean_object* v_u_1015_; lean_object* v_semiringInst_1016_; lean_object* v___x_1017_; 
lean_del_object(v___x_1006_);
v_type_1014_ = lean_ctor_get(v_toRing_1008_, 1);
lean_inc_ref(v_type_1014_);
v_u_1015_ = lean_ctor_get(v_toRing_1008_, 2);
lean_inc(v_u_1015_);
v_semiringInst_1016_ = lean_ctor_get(v_toRing_1008_, 4);
lean_inc_ref(v_semiringInst_1016_);
lean_dec_ref(v_toRing_1008_);
v___x_1017_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1015_, v_type_1014_, v_semiringInst_1016_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_n(v_a_1018_, 2);
lean_dec_ref_known(v___x_1017_, 1);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1019_, 0, v_a_1018_);
v___x_1020_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1019_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v___x_1020_, 0);
lean_dec(v_unused_1028_);
v___x_1022_ = v___x_1020_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v___x_1020_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_a_1018_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1018_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_a_1018_);
v_a_1029_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1020_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1020_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1003_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1003_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1104_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_toRing_1077_; lean_object* v_vars_1078_; lean_object* v_x_1079_; lean_object* v_k_1080_; lean_object* v___y_1082_; lean_object* v_size_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_toRing_1077_ = lean_ctor_get(v_a_1073_, 0);
lean_inc_ref(v_toRing_1077_);
lean_dec(v_a_1073_);
v_vars_1078_ = lean_ctor_get(v_toRing_1077_, 14);
lean_inc_ref(v_vars_1078_);
lean_dec_ref(v_toRing_1077_);
v_x_1079_ = lean_ctor_get(v_pw_1059_, 0);
lean_inc(v_x_1079_);
v_k_1080_ = lean_ctor_get(v_pw_1059_, 1);
lean_inc(v_k_1080_);
lean_dec_ref(v_pw_1059_);
v_size_1099_ = lean_ctor_get(v_vars_1078_, 2);
v___x_1100_ = l_Lean_instInhabitedExpr;
v___x_1101_ = lean_nat_dec_lt(v_x_1079_, v_size_1099_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v_x_1079_);
lean_dec_ref(v_vars_1078_);
v___x_1102_ = l_outOfBounds___redArg(v___x_1100_);
v___y_1082_ = v___x_1102_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1100_, v_vars_1078_, v_x_1079_);
lean_dec(v_x_1079_);
lean_dec_ref(v_vars_1078_);
v___y_1082_ = v___x_1103_;
goto v___jp_1081_;
}
v___jp_1081_:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_dec_eq(v_k_1080_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_del_object(v___x_1075_);
v___x_1085_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1095_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = l_Lean_mkNatLit(v_k_1080_);
v___x_1091_ = l_Lean_mkAppB(v_a_1086_, v___y_1082_, v___x_1090_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_dec_ref(v___y_1082_);
lean_dec(v_k_1080_);
return v___x_1085_;
}
}
else
{
lean_object* v___x_1097_; 
lean_dec(v_k_1080_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___y_1082_);
v___x_1097_ = v___x_1075_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___y_1082_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_pw_1059_);
v_a_1105_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1072_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1072_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_m_1127_, lean_object* v_acc_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
if (lean_obj_tag(v_m_1127_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_acc_1128_);
return v___x_1141_;
}
else
{
lean_object* v_p_1142_; lean_object* v_m_1143_; lean_object* v___x_1144_; 
v_p_1142_ = lean_ctor_get(v_m_1127_, 0);
lean_inc_ref(v_p_1142_);
v_m_1143_ = lean_ctor_get(v_m_1127_, 1);
lean_inc(v_m_1143_);
lean_dec_ref_known(v_m_1127_, 2);
v___x_1144_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1142_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = l_Lean_mkAppB(v_a_1145_, v_acc_1128_, v_a_1147_);
v_m_1127_ = v_m_1143_;
v_acc_1128_ = v___x_1148_;
goto _start;
}
else
{
lean_dec(v_a_1145_);
lean_dec(v_m_1143_);
lean_dec_ref(v_acc_1128_);
return v___x_1146_;
}
}
else
{
lean_dec(v_m_1143_);
lean_dec_ref(v_p_1142_);
lean_dec_ref(v_acc_1128_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_m_1150_, lean_object* v_acc_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1150_, v_acc_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_to_int(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_m_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
if (lean_obj_tag(v_m_1167_) == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1181_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1180_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1181_;
}
else
{
lean_object* v_p_1182_; lean_object* v_m_1183_; lean_object* v___x_1184_; 
v_p_1182_ = lean_ctor_get(v_m_1167_, 0);
lean_inc_ref(v_p_1182_);
v_m_1183_ = lean_ctor_get(v_m_1167_, 1);
lean_inc(v_m_1183_);
lean_dec_ref_known(v_m_1167_, 2);
v___x_1184_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1182_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1183_, v_a_1185_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1186_;
}
else
{
lean_dec(v_m_1183_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_m_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1201_, lean_object* v_m_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1216_ = lean_int_dec_eq(v_k_1201_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1201_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l_Lean_mkAppB(v_a_1218_, v_a_1220_, v_a_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_dec(v_a_1220_);
lean_dec(v_a_1218_);
return v___x_1221_;
}
}
else
{
lean_dec(v_a_1218_);
lean_dec(v_m_1202_);
return v___x_1219_;
}
}
else
{
lean_dec(v_m_1202_);
return v___x_1217_;
}
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1232_, lean_object* v_m_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1232_, v_m_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v_k_1232_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_1247_, lean_object* v_s_1248_){
_start:
{
lean_object* v_toRing_1249_; lean_object* v_invFn_x3f_1250_; lean_object* v_semiringId_x3f_1251_; lean_object* v_commSemiringInst_1252_; lean_object* v_commRingInst_1253_; lean_object* v_noZeroDivInst_x3f_1254_; lean_object* v_fieldInst_x3f_1255_; lean_object* v_powIdentityInst_x3f_1256_; lean_object* v_denoteEntries_1257_; lean_object* v_nextId_1258_; lean_object* v_steps_1259_; lean_object* v_queue_1260_; lean_object* v_basis_1261_; lean_object* v_diseqs_1262_; uint8_t v_recheck_1263_; lean_object* v_invSet_1264_; lean_object* v_powIdentityVarCount_1265_; lean_object* v_numEq0_x3f_1266_; uint8_t v_numEq0Updated_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1299_; 
v_toRing_1249_ = lean_ctor_get(v_s_1248_, 0);
v_invFn_x3f_1250_ = lean_ctor_get(v_s_1248_, 1);
v_semiringId_x3f_1251_ = lean_ctor_get(v_s_1248_, 2);
v_commSemiringInst_1252_ = lean_ctor_get(v_s_1248_, 3);
v_commRingInst_1253_ = lean_ctor_get(v_s_1248_, 4);
v_noZeroDivInst_x3f_1254_ = lean_ctor_get(v_s_1248_, 5);
v_fieldInst_x3f_1255_ = lean_ctor_get(v_s_1248_, 6);
v_powIdentityInst_x3f_1256_ = lean_ctor_get(v_s_1248_, 7);
v_denoteEntries_1257_ = lean_ctor_get(v_s_1248_, 8);
v_nextId_1258_ = lean_ctor_get(v_s_1248_, 9);
v_steps_1259_ = lean_ctor_get(v_s_1248_, 10);
v_queue_1260_ = lean_ctor_get(v_s_1248_, 11);
v_basis_1261_ = lean_ctor_get(v_s_1248_, 12);
v_diseqs_1262_ = lean_ctor_get(v_s_1248_, 13);
v_recheck_1263_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*17);
v_invSet_1264_ = lean_ctor_get(v_s_1248_, 14);
v_powIdentityVarCount_1265_ = lean_ctor_get(v_s_1248_, 15);
v_numEq0_x3f_1266_ = lean_ctor_get(v_s_1248_, 16);
v_numEq0Updated_1267_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*17 + 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_s_1248_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1269_ = v_s_1248_;
v_isShared_1270_ = v_isSharedCheck_1299_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_numEq0_x3f_1266_);
lean_inc(v_powIdentityVarCount_1265_);
lean_inc(v_invSet_1264_);
lean_inc(v_diseqs_1262_);
lean_inc(v_basis_1261_);
lean_inc(v_queue_1260_);
lean_inc(v_steps_1259_);
lean_inc(v_nextId_1258_);
lean_inc(v_denoteEntries_1257_);
lean_inc(v_powIdentityInst_x3f_1256_);
lean_inc(v_fieldInst_x3f_1255_);
lean_inc(v_noZeroDivInst_x3f_1254_);
lean_inc(v_commRingInst_1253_);
lean_inc(v_commSemiringInst_1252_);
lean_inc(v_semiringId_x3f_1251_);
lean_inc(v_invFn_x3f_1250_);
lean_inc(v_toRing_1249_);
lean_dec(v_s_1248_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1299_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_id_1271_; lean_object* v_type_1272_; lean_object* v_u_1273_; lean_object* v_ringInst_1274_; lean_object* v_semiringInst_1275_; lean_object* v_charInst_x3f_1276_; lean_object* v_mulFn_x3f_1277_; lean_object* v_subFn_x3f_1278_; lean_object* v_negFn_x3f_1279_; lean_object* v_powFn_x3f_1280_; lean_object* v_intCastFn_x3f_1281_; lean_object* v_natCastFn_x3f_1282_; lean_object* v_one_x3f_1283_; lean_object* v_vars_1284_; lean_object* v_varMap_1285_; lean_object* v_denote_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1297_; 
v_id_1271_ = lean_ctor_get(v_toRing_1249_, 0);
v_type_1272_ = lean_ctor_get(v_toRing_1249_, 1);
v_u_1273_ = lean_ctor_get(v_toRing_1249_, 2);
v_ringInst_1274_ = lean_ctor_get(v_toRing_1249_, 3);
v_semiringInst_1275_ = lean_ctor_get(v_toRing_1249_, 4);
v_charInst_x3f_1276_ = lean_ctor_get(v_toRing_1249_, 5);
v_mulFn_x3f_1277_ = lean_ctor_get(v_toRing_1249_, 7);
v_subFn_x3f_1278_ = lean_ctor_get(v_toRing_1249_, 8);
v_negFn_x3f_1279_ = lean_ctor_get(v_toRing_1249_, 9);
v_powFn_x3f_1280_ = lean_ctor_get(v_toRing_1249_, 10);
v_intCastFn_x3f_1281_ = lean_ctor_get(v_toRing_1249_, 11);
v_natCastFn_x3f_1282_ = lean_ctor_get(v_toRing_1249_, 12);
v_one_x3f_1283_ = lean_ctor_get(v_toRing_1249_, 13);
v_vars_1284_ = lean_ctor_get(v_toRing_1249_, 14);
v_varMap_1285_ = lean_ctor_get(v_toRing_1249_, 15);
v_denote_1286_ = lean_ctor_get(v_toRing_1249_, 16);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_toRing_1249_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_toRing_1249_, 6);
lean_dec(v_unused_1298_);
v___x_1288_ = v_toRing_1249_;
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_denote_1286_);
lean_inc(v_varMap_1285_);
lean_inc(v_vars_1284_);
lean_inc(v_one_x3f_1283_);
lean_inc(v_natCastFn_x3f_1282_);
lean_inc(v_intCastFn_x3f_1281_);
lean_inc(v_powFn_x3f_1280_);
lean_inc(v_negFn_x3f_1279_);
lean_inc(v_subFn_x3f_1278_);
lean_inc(v_mulFn_x3f_1277_);
lean_inc(v_charInst_x3f_1276_);
lean_inc(v_semiringInst_1275_);
lean_inc(v_ringInst_1274_);
lean_inc(v_u_1273_);
lean_inc(v_type_1272_);
lean_inc(v_id_1271_);
lean_dec(v_toRing_1249_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_a_1247_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 6, v___x_1290_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_id_1271_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_type_1272_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_u_1273_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_ringInst_1274_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_semiringInst_1275_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v_charInst_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1296_, 6, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 7, v_mulFn_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1296_, 8, v_subFn_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1296_, 9, v_negFn_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1296_, 10, v_powFn_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1296_, 11, v_intCastFn_x3f_1281_);
lean_ctor_set(v_reuseFailAlloc_1296_, 12, v_natCastFn_x3f_1282_);
lean_ctor_set(v_reuseFailAlloc_1296_, 13, v_one_x3f_1283_);
lean_ctor_set(v_reuseFailAlloc_1296_, 14, v_vars_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 15, v_varMap_1285_);
lean_ctor_set(v_reuseFailAlloc_1296_, 16, v_denote_1286_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1292_);
v___x_1294_ = v___x_1269_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_invFn_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_semiringId_x3f_1251_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_commSemiringInst_1252_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_commRingInst_1253_);
lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_noZeroDivInst_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_fieldInst_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_powIdentityInst_x3f_1256_);
lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_denoteEntries_1257_);
lean_ctor_set(v_reuseFailAlloc_1295_, 9, v_nextId_1258_);
lean_ctor_set(v_reuseFailAlloc_1295_, 10, v_steps_1259_);
lean_ctor_set(v_reuseFailAlloc_1295_, 11, v_queue_1260_);
lean_ctor_set(v_reuseFailAlloc_1295_, 12, v_basis_1261_);
lean_ctor_set(v_reuseFailAlloc_1295_, 13, v_diseqs_1262_);
lean_ctor_set(v_reuseFailAlloc_1295_, 14, v_invSet_1264_);
lean_ctor_set(v_reuseFailAlloc_1295_, 15, v_powIdentityVarCount_1265_);
lean_ctor_set(v_reuseFailAlloc_1295_, 16, v_numEq0_x3f_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*17, v_recheck_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*17 + 1, v_numEq0Updated_1267_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1372_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1372_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1372_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_toRing_1333_; lean_object* v_addFn_x3f_1334_; 
v_toRing_1333_ = lean_ctor_get(v_a_1329_, 0);
lean_inc_ref(v_toRing_1333_);
lean_dec(v_a_1329_);
v_addFn_x3f_1334_ = lean_ctor_get(v_toRing_1333_, 6);
if (lean_obj_tag(v_addFn_x3f_1334_) == 1)
{
lean_object* v_val_1335_; lean_object* v___x_1337_; 
lean_inc_ref(v_addFn_x3f_1334_);
lean_dec_ref(v_toRing_1333_);
v_val_1335_ = lean_ctor_get(v_addFn_x3f_1334_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_addFn_x3f_1334_, 1);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v_val_1335_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v_type_1339_; lean_object* v_u_1340_; lean_object* v_semiringInst_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_expectedInst_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_del_object(v___x_1331_);
v_type_1339_ = lean_ctor_get(v_toRing_1333_, 1);
lean_inc_ref_n(v_type_1339_, 3);
v_u_1340_ = lean_ctor_get(v_toRing_1333_, 2);
lean_inc_n(v_u_1340_, 2);
v_semiringInst_1341_ = lean_ctor_get(v_toRing_1333_, 4);
lean_inc_ref(v_semiringInst_1341_);
lean_dec_ref(v_toRing_1333_);
v___x_1342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_u_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_inc_ref(v___x_1344_);
v___x_1345_ = l_Lean_mkConst(v___x_1342_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3));
v___x_1347_ = l_Lean_mkConst(v___x_1346_, v___x_1344_);
v___x_1348_ = l_Lean_mkAppB(v___x_1347_, v_type_1339_, v_semiringInst_1341_);
v_expectedInst_1349_ = l_Lean_mkAppB(v___x_1345_, v_type_1339_, v___x_1348_);
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5));
v___x_1351_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7));
v___x_1352_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1339_, v_u_1340_, v___x_1350_, v___x_1351_, v_expectedInst_1349_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc_n(v_a_1353_, 2);
lean_dec_ref_known(v___x_1352_, 1);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_1354_, 0, v_a_1353_);
v___x_1355_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1354_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1355_, 0);
lean_dec(v_unused_1363_);
v___x_1357_ = v___x_1355_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1355_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_a_1353_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1353_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1353_);
v_a_1364_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1355_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1355_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1328_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1328_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1394_, lean_object* v_acc_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
if (lean_obj_tag(v_p_1394_) == 0)
{
lean_object* v_k_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1429_; 
v_k_1408_ = lean_ctor_get(v_p_1394_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_p_1394_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1410_ = v_p_1394_;
v_isShared_1411_ = v_isSharedCheck_1429_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_k_1408_);
lean_dec(v_p_1394_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1429_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1413_ = lean_int_dec_eq(v_k_1408_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_del_object(v___x_1410_);
v___x_1414_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1408_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v_k_1408_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_mkAppB(v_a_1415_, v_acc_1395_, v_a_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_dec(v_a_1415_);
lean_dec_ref(v_acc_1395_);
return v___x_1416_;
}
}
else
{
lean_dec(v_k_1408_);
lean_dec_ref(v_acc_1395_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_k_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_acc_1395_);
v___x_1427_ = v___x_1410_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_acc_1395_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_k_1430_; lean_object* v_v_1431_; lean_object* v_p_1432_; lean_object* v___x_1433_; 
v_k_1430_ = lean_ctor_get(v_p_1394_, 0);
lean_inc(v_k_1430_);
v_v_1431_ = lean_ctor_get(v_p_1394_, 1);
lean_inc(v_v_1431_);
v_p_1432_ = lean_ctor_get(v_p_1394_, 2);
lean_inc_ref(v_p_1432_);
lean_dec_ref_known(v_p_1394_, 3);
v___x_1433_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1430_, v_v_1431_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v_k_1430_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_mkAppB(v_a_1434_, v_acc_1395_, v_a_1436_);
v_p_1394_ = v_p_1432_;
v_acc_1395_ = v___x_1437_;
goto _start;
}
else
{
lean_dec(v_a_1434_);
lean_dec_ref(v_p_1432_);
lean_dec_ref(v_acc_1395_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_p_1432_);
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
lean_dec_ref(v_acc_1395_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1439_, lean_object* v_acc_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1439_, v_acc_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
if (lean_obj_tag(v_p_1454_) == 0)
{
lean_object* v_k_1467_; lean_object* v___x_1468_; 
v_k_1467_ = lean_ctor_get(v_p_1454_, 0);
lean_inc(v_k_1467_);
lean_dec_ref_known(v_p_1454_, 1);
v___x_1468_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1467_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v_k_1467_);
return v___x_1468_;
}
else
{
lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v_p_1471_; lean_object* v___x_1472_; 
v_k_1469_ = lean_ctor_get(v_p_1454_, 0);
lean_inc(v_k_1469_);
v_v_1470_ = lean_ctor_get(v_p_1454_, 1);
lean_inc(v_v_1470_);
v_p_1471_ = lean_ctor_get(v_p_1454_, 2);
lean_inc_ref(v_p_1471_);
lean_dec_ref_known(v_p_1454_, 3);
v___x_1472_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1469_, v_v_1470_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v_k_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1471_, v_a_1473_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1474_;
}
else
{
lean_dec_ref(v_p_1471_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1488_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1489_; double v___x_1490_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_float_of_nat(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_ref_1501_; lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1547_; 
v_ref_1501_ = lean_ctor_get(v___y_1498_, 5);
v___x_1502_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1547_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1547_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v_traceState_1508_; lean_object* v_env_1509_; lean_object* v_nextMacroScope_1510_; lean_object* v_ngen_1511_; lean_object* v_auxDeclNGen_1512_; lean_object* v_cache_1513_; lean_object* v_messages_1514_; lean_object* v_infoState_1515_; lean_object* v_snapshotTasks_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1546_; 
v___x_1507_ = lean_st_ref_take(v___y_1499_);
v_traceState_1508_ = lean_ctor_get(v___x_1507_, 4);
v_env_1509_ = lean_ctor_get(v___x_1507_, 0);
v_nextMacroScope_1510_ = lean_ctor_get(v___x_1507_, 1);
v_ngen_1511_ = lean_ctor_get(v___x_1507_, 2);
v_auxDeclNGen_1512_ = lean_ctor_get(v___x_1507_, 3);
v_cache_1513_ = lean_ctor_get(v___x_1507_, 5);
v_messages_1514_ = lean_ctor_get(v___x_1507_, 6);
v_infoState_1515_ = lean_ctor_get(v___x_1507_, 7);
v_snapshotTasks_1516_ = lean_ctor_get(v___x_1507_, 8);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1518_ = v___x_1507_;
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snapshotTasks_1516_);
lean_inc(v_infoState_1515_);
lean_inc(v_messages_1514_);
lean_inc(v_cache_1513_);
lean_inc(v_traceState_1508_);
lean_inc(v_auxDeclNGen_1512_);
lean_inc(v_ngen_1511_);
lean_inc(v_nextMacroScope_1510_);
lean_inc(v_env_1509_);
lean_dec(v___x_1507_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint64_t v_tid_1520_; lean_object* v_traces_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_tid_1520_ = lean_ctor_get_uint64(v_traceState_1508_, sizeof(void*)*1);
v_traces_1521_ = lean_ctor_get(v_traceState_1508_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_traceState_1508_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1523_ = v_traceState_1508_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_traces_1521_);
lean_dec(v_traceState_1508_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; double v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1527_ = 0;
v___x_1528_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1529_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1529_, 0, v_cls_1494_);
lean_ctor_set(v___x_1529_, 1, v___x_1525_);
lean_ctor_set(v___x_1529_, 2, v___x_1528_);
lean_ctor_set_float(v___x_1529_, sizeof(void*)*3, v___x_1526_);
lean_ctor_set_float(v___x_1529_, sizeof(void*)*3 + 8, v___x_1526_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*3 + 16, v___x_1527_);
v___x_1530_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1531_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v_a_1503_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
lean_inc(v_ref_1501_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_ref_1501_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_PersistentArray_push___redArg(v_traces_1521_, v___x_1532_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1533_);
v___x_1535_ = v___x_1523_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1533_);
lean_ctor_set_uint64(v_reuseFailAlloc_1544_, sizeof(void*)*1, v_tid_1520_);
v___x_1535_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1535_);
v___x_1537_ = v___x_1518_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_env_1509_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_nextMacroScope_1510_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_ngen_1511_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_auxDeclNGen_1512_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v_cache_1513_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_messages_1514_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_infoState_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_snapshotTasks_1516_);
v___x_1537_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_st_ref_set(v___y_1499_, v___x_1537_);
v___x_1539_ = lean_box(0);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1539_);
v___x_1541_ = v___x_1505_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1548_, v_msg_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1571_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1572_ = l_Lean_Name_append(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1576_, v_a_1577_, v_a_1585_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1814_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1814_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1814_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_unbox(v_a_1589_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v___x_1594_ = lean_box(0);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1594_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v___x_1598_; 
lean_del_object(v___x_1591_);
v___x_1598_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1805_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1805_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1805_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
if (lean_obj_tag(v_a_1599_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1604_; 
lean_del_object(v___x_1601_);
v_val_1603_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v_a_1599_, 1);
lean_inc_ref(v_p_1576_);
v___x_1604_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1576_, v_a_1577_, v_a_1585_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = l_Lean_Meta_Sym_canon(v_a_1605_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = l_Lean_Meta_Sym_shareCommon(v_a_1607_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
lean_inc_ref(v_p_1576_);
v___x_1610_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1576_, v_a_1577_, v_a_1585_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc_n(v_a_1611_, 2);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = 0;
v___x_1613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1613_, 0, v_val_1603_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*1, v___x_1612_);
v___x_1614_ = lean_unbox(v_a_1589_);
v___x_1615_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1609_, v___x_1614_, v_a_1611_, v___x_1613_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1760_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1760_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1760_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
if (lean_obj_tag(v_a_1616_) == 1)
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
lean_del_object(v___x_1618_);
v_val_1620_ = lean_ctor_get(v_a_1616_, 0);
lean_inc_n(v_val_1620_, 2);
lean_dec_ref_known(v_a_1616_, 1);
v___x_1621_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_val_1620_, v___x_1613_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1747_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1747_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1747_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
if (lean_obj_tag(v_a_1622_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1742_; 
lean_del_object(v___x_1624_);
v_val_1626_ = lean_ctor_get(v_a_1622_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1622_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1628_ = v_a_1622_;
v_isShared_1629_ = v_isSharedCheck_1742_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_val_1626_);
lean_dec(v_a_1622_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1742_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; 
lean_inc(v_val_1626_);
v___x_1630_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1626_, v___x_1613_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec_ref_known(v___x_1613_, 1);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1631_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_n(v_a_1633_, 2);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1586_);
lean_inc_ref(v_a_1585_);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
lean_inc(v_a_1580_);
lean_inc_ref(v_a_1579_);
lean_inc(v_a_1578_);
lean_inc(v_a_1577_);
v___x_1635_ = lean_grind_internalize(v_a_1633_, v_a_1611_, v___x_1634_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1716_; 
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1717_);
v___x_1637_ = v___x_1635_;
v_isShared_1638_ = v_isSharedCheck_1716_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v___x_1635_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1716_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1633_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1707_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1707_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1707_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
uint8_t v___x_1653_; 
v___x_1653_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1576_, v_a_1640_);
if (v___x_1653_ == 0)
{
lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_del_object(v___x_1637_);
v___f_1654_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1654_, 0, v_a_1589_);
v___x_1655_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1656_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1655_, v___f_1654_, v_a_1577_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_options_1657_; uint8_t v_hasTrace_1658_; 
lean_dec_ref_known(v___x_1656_, 1);
v_options_1657_ = lean_ctor_get(v_a_1585_, 2);
v_hasTrace_1658_ = lean_ctor_get_uint8(v_options_1657_, sizeof(void*)*1);
if (v_hasTrace_1658_ == 0)
{
lean_dec_ref(v_p_1576_);
goto v___jp_1644_;
}
else
{
lean_object* v_inheritedTraceOptions_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_inheritedTraceOptions_1659_ = lean_ctor_get(v_a_1585_, 13);
v___x_1660_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1661_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1659_, v_options_1657_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_p_1576_);
goto v___jp_1644_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1576_, v_a_1577_, v_a_1585_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
lean_inc(v_a_1640_);
v___x_1665_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1640_, v_a_1577_, v_a_1585_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_a_1664_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_a_1666_);
v___x_1670_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1660_, v___x_1669_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_dec_ref_known(v___x_1670_, 1);
goto v___jp_1644_;
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_a_1664_);
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
v_a_1679_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1665_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1665_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
v_a_1687_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1663_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1663_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec_ref(v_p_1576_);
v_a_1695_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1656_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1656_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v___x_1703_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1703_);
v___x_1705_ = v___x_1637_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
v___jp_1644_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_val_1626_);
lean_ctor_set(v___x_1645_, 1, v_a_1640_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_val_1620_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1646_);
v___x_1648_ = v___x_1628_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1648_);
v___x_1650_ = v___x_1642_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_del_object(v___x_1637_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1708_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1639_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1639_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1633_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1718_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1635_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1635_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1726_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1632_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1632_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_del_object(v___x_1628_);
lean_dec(v_val_1626_);
lean_dec(v_val_1620_);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1734_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1630_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1630_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec(v_a_1622_);
lean_dec(v_val_1620_);
lean_dec_ref_known(v___x_1613_, 1);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v___x_1743_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1743_);
v___x_1745_ = v___x_1624_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_val_1620_);
lean_dec_ref_known(v___x_1613_, 1);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1748_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1621_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1621_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v_a_1616_);
lean_dec_ref_known(v___x_1613_, 1);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v___x_1756_ = lean_box(0);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1756_);
v___x_1758_ = v___x_1618_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref_known(v___x_1613_, 1);
lean_dec(v_a_1611_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1761_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1615_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1615_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1609_);
lean_dec(v_val_1603_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1769_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1610_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1610_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_val_1603_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1777_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1608_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1608_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_val_1603_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1785_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1606_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1606_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_val_1603_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1793_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1604_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1604_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v___x_1801_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1801_);
v___x_1803_ = v___x_1601_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1589_);
lean_dec_ref(v_p_1576_);
v_a_1806_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1598_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1598_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v_p_1576_);
v_a_1815_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1588_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1588_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec(v_a_1824_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1836_, v_msg_1837_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1867_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_msg_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1881_, v_msg_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1895_;
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
