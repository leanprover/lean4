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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPolyM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg(lean_object* v_p_11_, lean_object* v_a_12_, lean_object* v_a_13_){
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
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isNonlinear___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_11_ = stack[0].m_obj;
lean_object* v_a_12_ = stack[1].m_obj;
lean_object* v_a_13_ = stack[2].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_11_, v_a_12_, v_a_13_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___redArg___boxed(lean_object* v_p_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_p_56_);
return v_res_60_;
}
}
lean_object* l_Int_Internal_Linear_Poly_isNonlinear(lean_object* v_p_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_61_, v_a_62_, v_a_70_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isNonlinear_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_61_ = stack[0].m_obj;
lean_object* v_a_62_ = stack[1].m_obj;
lean_object* v_a_63_ = stack[2].m_obj;
lean_object* v_a_64_ = stack[3].m_obj;
lean_object* v_a_65_ = stack[4].m_obj;
lean_object* v_a_66_ = stack[5].m_obj;
lean_object* v_a_67_ = stack[6].m_obj;
lean_object* v_a_68_ = stack[7].m_obj;
lean_object* v_a_69_ = stack[8].m_obj;
lean_object* v_a_70_ = stack[9].m_obj;
lean_object* v_a_71_ = stack[10].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Int_Internal_Linear_Poly_isNonlinear(v_p_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNonlinear___boxed(lean_object* v_p_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Int_Internal_Linear_Poly_isNonlinear(v_p_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_p_75_);
return v_res_87_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
if (lean_obj_tag(v_a_88_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_isSharedCheck_99_ = !lean_is_exclusive(v_a_88_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v_a_88_, 0);
lean_dec(v_unused_100_);
v___x_94_ = v_a_88_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_dec(v_a_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_a_89_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_89_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_object* v_v_101_; lean_object* v_p_102_; lean_object* v___x_103_; 
v_v_101_ = lean_ctor_get(v_a_88_, 1);
lean_inc(v_v_101_);
v_p_102_ = lean_ctor_get(v_a_88_, 2);
lean_inc_ref(v_p_102_);
lean_dec_ref_known(v_a_88_, 3);
v___x_103_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_101_, v_a_90_, v_a_91_);
lean_dec(v_v_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_104_, v_a_90_);
lean_dec(v_a_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; uint8_t v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = lean_nat_dec_le(v_a_106_, v_a_89_);
if (v___x_107_ == 0)
{
lean_dec(v_a_89_);
v_a_88_ = v_p_102_;
v_a_89_ = v_a_106_;
goto _start;
}
else
{
lean_dec(v_a_106_);
v_a_88_ = v_p_102_;
goto _start;
}
}
else
{
lean_dec_ref(v_p_102_);
lean_dec(v_a_89_);
return v___x_105_;
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_p_102_);
lean_dec(v_a_89_);
v_a_110_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_103_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_103_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_res_118_;
v_res_118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_a_88_, v_a_89_, v_a_90_, v_a_91_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg___boxed(lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
return v_res_124_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_a_125_, v_a_126_, v_a_127_, v_a_135_);
return v___x_138_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_125_ = stack[0].m_obj;
lean_object* v_a_126_ = stack[1].m_obj;
lean_object* v_a_127_ = stack[2].m_obj;
lean_object* v_a_128_ = stack[3].m_obj;
lean_object* v_a_129_ = stack[4].m_obj;
lean_object* v_a_130_ = stack[5].m_obj;
lean_object* v_a_131_ = stack[6].m_obj;
lean_object* v_a_132_ = stack[7].m_obj;
lean_object* v_a_133_ = stack[8].m_obj;
lean_object* v_a_134_ = stack[9].m_obj;
lean_object* v_a_135_ = stack[10].m_obj;
lean_object* v_a_136_ = stack[11].m_obj;
lean_object* v_res_139_;
v_res_139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___boxed(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go(v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec(v_a_142_);
return v_res_153_;
}
}
lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg(lean_object* v_p_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Internal_Linear_Poly_getGeneration_go___redArg(v_p_154_, v___x_158_, v_a_155_, v_a_156_);
return v___x_159_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_getGeneration___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_154_ = stack[0].m_obj;
lean_object* v_a_155_ = stack[1].m_obj;
lean_object* v_a_156_ = stack[2].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_154_, v_a_155_, v_a_156_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___redArg___boxed(lean_object* v_p_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_161_, v_a_162_, v_a_163_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
return v_res_165_;
}
}
lean_object* l_Int_Internal_Linear_Poly_getGeneration(lean_object* v_p_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_166_, v_a_167_, v_a_175_);
return v___x_178_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_getGeneration_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_166_ = stack[0].m_obj;
lean_object* v_a_167_ = stack[1].m_obj;
lean_object* v_a_168_ = stack[2].m_obj;
lean_object* v_a_169_ = stack[3].m_obj;
lean_object* v_a_170_ = stack[4].m_obj;
lean_object* v_a_171_ = stack[5].m_obj;
lean_object* v_a_172_ = stack[6].m_obj;
lean_object* v_a_173_ = stack[7].m_obj;
lean_object* v_a_174_ = stack[8].m_obj;
lean_object* v_a_175_ = stack[9].m_obj;
lean_object* v_a_176_ = stack[10].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Int_Internal_Linear_Poly_getGeneration(v_p_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getGeneration___boxed(lean_object* v_p_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Int_Internal_Linear_Poly_getGeneration(v_p_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec(v_a_181_);
return v_res_192_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_193_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_a_201_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_200_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_193_ = stack[0].m_obj;
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_a_198_ = stack[5].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg___boxed(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_219_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_220_ = stack[0].m_obj;
lean_object* v_a_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_a_226_ = stack[6].m_obj;
lean_object* v_a_227_ = stack[7].m_obj;
lean_object* v_a_228_ = stack[8].m_obj;
lean_object* v_a_229_ = stack[9].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec(v_a_233_);
return v_res_244_;
}
}
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(uint8_t v_a_245_, lean_object* v_s_246_){
_start:
{
lean_object* v_vars_247_; lean_object* v_varMap_248_; lean_object* v_varsHistory_249_; lean_object* v_natToIntMap_250_; lean_object* v_natDef_251_; lean_object* v_dvds_252_; lean_object* v_lowers_253_; lean_object* v_uppers_254_; lean_object* v_diseqs_255_; lean_object* v_elimEqs_256_; lean_object* v_elimStack_257_; lean_object* v_occurs_258_; lean_object* v_assignment_259_; lean_object* v_nextCnstrId_260_; uint8_t v_caseSplits_261_; lean_object* v_steps_262_; lean_object* v_conflict_x3f_263_; lean_object* v_diseqSplits_264_; lean_object* v_divMod_265_; lean_object* v_nonlinearOccs_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_vars_247_ = lean_ctor_get(v_s_246_, 0);
v_varMap_248_ = lean_ctor_get(v_s_246_, 1);
v_varsHistory_249_ = lean_ctor_get(v_s_246_, 2);
v_natToIntMap_250_ = lean_ctor_get(v_s_246_, 3);
v_natDef_251_ = lean_ctor_get(v_s_246_, 4);
v_dvds_252_ = lean_ctor_get(v_s_246_, 5);
v_lowers_253_ = lean_ctor_get(v_s_246_, 6);
v_uppers_254_ = lean_ctor_get(v_s_246_, 7);
v_diseqs_255_ = lean_ctor_get(v_s_246_, 8);
v_elimEqs_256_ = lean_ctor_get(v_s_246_, 9);
v_elimStack_257_ = lean_ctor_get(v_s_246_, 10);
v_occurs_258_ = lean_ctor_get(v_s_246_, 11);
v_assignment_259_ = lean_ctor_get(v_s_246_, 12);
v_nextCnstrId_260_ = lean_ctor_get(v_s_246_, 13);
v_caseSplits_261_ = lean_ctor_get_uint8(v_s_246_, sizeof(void*)*19);
v_steps_262_ = lean_ctor_get(v_s_246_, 14);
v_conflict_x3f_263_ = lean_ctor_get(v_s_246_, 15);
v_diseqSplits_264_ = lean_ctor_get(v_s_246_, 16);
v_divMod_265_ = lean_ctor_get(v_s_246_, 17);
v_nonlinearOccs_266_ = lean_ctor_get(v_s_246_, 18);
v_isSharedCheck_273_ = !lean_is_exclusive(v_s_246_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v_s_246_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_nonlinearOccs_266_);
lean_inc(v_divMod_265_);
lean_inc(v_diseqSplits_264_);
lean_inc(v_conflict_x3f_263_);
lean_inc(v_steps_262_);
lean_inc(v_nextCnstrId_260_);
lean_inc(v_assignment_259_);
lean_inc(v_occurs_258_);
lean_inc(v_elimStack_257_);
lean_inc(v_elimEqs_256_);
lean_inc(v_diseqs_255_);
lean_inc(v_uppers_254_);
lean_inc(v_lowers_253_);
lean_inc(v_dvds_252_);
lean_inc(v_natDef_251_);
lean_inc(v_natToIntMap_250_);
lean_inc(v_varsHistory_249_);
lean_inc(v_varMap_248_);
lean_inc(v_vars_247_);
lean_dec(v_s_246_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_vars_247_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_varMap_248_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_varsHistory_249_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_natToIntMap_250_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_natDef_251_);
lean_ctor_set(v_reuseFailAlloc_272_, 5, v_dvds_252_);
lean_ctor_set(v_reuseFailAlloc_272_, 6, v_lowers_253_);
lean_ctor_set(v_reuseFailAlloc_272_, 7, v_uppers_254_);
lean_ctor_set(v_reuseFailAlloc_272_, 8, v_diseqs_255_);
lean_ctor_set(v_reuseFailAlloc_272_, 9, v_elimEqs_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 10, v_elimStack_257_);
lean_ctor_set(v_reuseFailAlloc_272_, 11, v_occurs_258_);
lean_ctor_set(v_reuseFailAlloc_272_, 12, v_assignment_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 13, v_nextCnstrId_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 14, v_steps_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 15, v_conflict_x3f_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 16, v_diseqSplits_264_);
lean_ctor_set(v_reuseFailAlloc_272_, 17, v_divMod_265_);
lean_ctor_set(v_reuseFailAlloc_272_, 18, v_nonlinearOccs_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*19, v_caseSplits_261_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*19 + 1, v_a_245_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_245_ = stack[0].m_num;
lean_object* v_s_246_ = stack[1].m_obj;
lean_object* v_res_274_;
v_res_274_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_245_, v_s_246_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_275_, lean_object* v_s_276_){
_start:
{
uint8_t v_a_124155__boxed_277_; lean_object* v_res_278_; 
v_a_124155__boxed_277_ = lean_unbox(v_a_275_);
v_res_278_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_124155__boxed_277_, v_s_276_);
return v_res_278_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v_env_286_; uint8_t v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v_toCold_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_285_ = lean_st_ref_get(v___y_283_);
v_env_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_env_286_);
lean_dec(v___x_285_);
v___x_287_ = 0;
v_env_288_ = l_Lean_Environment_setRecordingDeps(v_env_286_, v___x_287_);
v___x_289_ = lean_st_ref_get(v___y_281_);
v_toCold_290_ = lean_ctor_get(v___y_282_, 0);
v_mctx_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_289_);
v_lctx_292_ = lean_ctor_get(v___y_280_, 2);
v_options_293_ = lean_ctor_get(v_toCold_290_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_288_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_279_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_279_ = stack[0].m_obj;
lean_object* v___y_280_ = stack[1].m_obj;
lean_object* v___y_281_ = stack[2].m_obj;
lean_object* v___y_282_ = stack[3].m_obj;
lean_object* v___y_283_ = stack[4].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_ref_311_; lean_object* v___x_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_ref_311_ = lean_ctor_get(v___y_308_, 2);
v___x_312_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_inc(v_ref_311_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_ref_311_);
lean_ctor_set(v___x_317_, 1, v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_305_ = stack[0].m_obj;
lean_object* v___y_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
lean_inc_ref(v_type_333_);
v___x_346_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_333_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_359_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
if (lean_obj_tag(v_a_347_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_353_; 
lean_dec_ref(v_type_333_);
v_val_351_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_a_347_, 1);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_val_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_del_object(v___x_349_);
lean_dec(v_a_347_);
v___x_355_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_356_ = l_Lean_indentExpr(v_type_333_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_357_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_358_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_type_333_);
v_a_360_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_346_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_346_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_333_ = stack[0].m_obj;
lean_object* v___y_334_ = stack[1].m_obj;
lean_object* v___y_335_ = stack[2].m_obj;
lean_object* v___y_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v___y_338_ = stack[5].m_obj;
lean_object* v___y_339_ = stack[6].m_obj;
lean_object* v___y_340_ = stack[7].m_obj;
lean_object* v___y_341_ = stack[8].m_obj;
lean_object* v___y_342_ = stack[9].m_obj;
lean_object* v___y_343_ = stack[10].m_obj;
lean_object* v___y_344_ = stack[11].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_382_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_383_, lean_object* v_u_384_, lean_object* v_instDeclName_385_, lean_object* v_declName_386_, lean_object* v_expectedInst_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_400_ = lean_box(0);
lean_inc_n(v_u_384_, 2);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v_u_384_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v_u_384_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v_u_384_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_inc_ref(v___x_403_);
v___x_404_ = l_Lean_mkConst(v_instDeclName_385_, v___x_403_);
lean_inc_ref_n(v_type_383_, 3);
v___x_405_ = l_Lean_mkApp3(v___x_404_, v_type_383_, v_type_383_, v_type_383_);
v___x_406_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_405_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc_n(v_a_407_, 2);
lean_dec_ref_known(v___x_406_, 1);
lean_inc(v_declName_386_);
v___x_408_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_386_, v_a_407_, v_expectedInst_387_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_409_ = l_Lean_mkConst(v_declName_386_, v___x_403_);
lean_inc_ref_n(v_type_383_, 2);
v___x_410_ = l_Lean_mkApp4(v___x_409_, v_type_383_, v_type_383_, v_type_383_, v_a_407_);
v___x_411_ = l_Lean_Meta_Sym_canon(v___x_410_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_Sym_shareCommon(v_a_412_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v___x_413_;
}
else
{
return v___x_411_;
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_407_);
lean_dec_ref_known(v___x_403_, 2);
lean_dec(v_declName_386_);
lean_dec_ref(v_type_383_);
v_a_414_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_408_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_403_, 2);
lean_dec_ref(v_expectedInst_387_);
lean_dec(v_declName_386_);
lean_dec_ref(v_type_383_);
return v___x_406_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_383_ = stack[0].m_obj;
lean_object* v_u_384_ = stack[1].m_obj;
lean_object* v_instDeclName_385_ = stack[2].m_obj;
lean_object* v_declName_386_ = stack[3].m_obj;
lean_object* v_expectedInst_387_ = stack[4].m_obj;
lean_object* v___y_388_ = stack[5].m_obj;
lean_object* v___y_389_ = stack[6].m_obj;
lean_object* v___y_390_ = stack[7].m_obj;
lean_object* v___y_391_ = stack[8].m_obj;
lean_object* v___y_392_ = stack[9].m_obj;
lean_object* v___y_393_ = stack[10].m_obj;
lean_object* v___y_394_ = stack[11].m_obj;
lean_object* v___y_395_ = stack[12].m_obj;
lean_object* v___y_396_ = stack[13].m_obj;
lean_object* v___y_397_ = stack[14].m_obj;
lean_object* v___y_398_ = stack[15].m_obj;
lean_object* v_res_422_;
v_res_422_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_383_, v_u_384_, v_instDeclName_385_, v_declName_386_, v_expectedInst_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_423_ = _args[0];
lean_object* v_u_424_ = _args[1];
lean_object* v_instDeclName_425_ = _args[2];
lean_object* v_declName_426_ = _args[3];
lean_object* v_expectedInst_427_ = _args[4];
lean_object* v___y_428_ = _args[5];
lean_object* v___y_429_ = _args[6];
lean_object* v___y_430_ = _args[7];
lean_object* v___y_431_ = _args[8];
lean_object* v___y_432_ = _args[9];
lean_object* v___y_433_ = _args[10];
lean_object* v___y_434_ = _args[11];
lean_object* v___y_435_ = _args[12];
lean_object* v___y_436_ = _args[13];
lean_object* v___y_437_ = _args[14];
lean_object* v___y_438_ = _args[15];
lean_object* v___y_439_ = _args[16];
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_423_, v_u_424_, v_instDeclName_425_, v_declName_426_, v_expectedInst_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_441_, lean_object* v_s_442_){
_start:
{
lean_object* v_toRing_443_; lean_object* v_invFn_x3f_444_; lean_object* v_divFn_x3f_445_; lean_object* v_semiringId_x3f_446_; lean_object* v_commSemiringInst_447_; lean_object* v_commRingInst_448_; lean_object* v_noZeroDivInst_x3f_449_; lean_object* v_fieldInst_x3f_450_; lean_object* v_powIdentityInst_x3f_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_482_; 
v_toRing_443_ = lean_ctor_get(v_s_442_, 0);
v_invFn_x3f_444_ = lean_ctor_get(v_s_442_, 1);
v_divFn_x3f_445_ = lean_ctor_get(v_s_442_, 2);
v_semiringId_x3f_446_ = lean_ctor_get(v_s_442_, 3);
v_commSemiringInst_447_ = lean_ctor_get(v_s_442_, 4);
v_commRingInst_448_ = lean_ctor_get(v_s_442_, 5);
v_noZeroDivInst_x3f_449_ = lean_ctor_get(v_s_442_, 6);
v_fieldInst_x3f_450_ = lean_ctor_get(v_s_442_, 7);
v_powIdentityInst_x3f_451_ = lean_ctor_get(v_s_442_, 8);
v_isSharedCheck_482_ = !lean_is_exclusive(v_s_442_);
if (v_isSharedCheck_482_ == 0)
{
v___x_453_ = v_s_442_;
v_isShared_454_ = v_isSharedCheck_482_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_powIdentityInst_x3f_451_);
lean_inc(v_fieldInst_x3f_450_);
lean_inc(v_noZeroDivInst_x3f_449_);
lean_inc(v_commRingInst_448_);
lean_inc(v_commSemiringInst_447_);
lean_inc(v_semiringId_x3f_446_);
lean_inc(v_divFn_x3f_445_);
lean_inc(v_invFn_x3f_444_);
lean_inc(v_toRing_443_);
lean_dec(v_s_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_482_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_id_455_; lean_object* v_type_456_; lean_object* v_u_457_; lean_object* v_ringInst_458_; lean_object* v_semiringInst_459_; lean_object* v_charInst_x3f_460_; lean_object* v_mulFn_x3f_461_; lean_object* v_subFn_x3f_462_; lean_object* v_negFn_x3f_463_; lean_object* v_powFn_x3f_464_; lean_object* v_intCastFn_x3f_465_; lean_object* v_natCastFn_x3f_466_; lean_object* v_natSMulFn_x3f_467_; lean_object* v_intSMulFn_x3f_468_; lean_object* v_one_x3f_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_480_; 
v_id_455_ = lean_ctor_get(v_toRing_443_, 0);
v_type_456_ = lean_ctor_get(v_toRing_443_, 1);
v_u_457_ = lean_ctor_get(v_toRing_443_, 2);
v_ringInst_458_ = lean_ctor_get(v_toRing_443_, 3);
v_semiringInst_459_ = lean_ctor_get(v_toRing_443_, 4);
v_charInst_x3f_460_ = lean_ctor_get(v_toRing_443_, 5);
v_mulFn_x3f_461_ = lean_ctor_get(v_toRing_443_, 7);
v_subFn_x3f_462_ = lean_ctor_get(v_toRing_443_, 8);
v_negFn_x3f_463_ = lean_ctor_get(v_toRing_443_, 9);
v_powFn_x3f_464_ = lean_ctor_get(v_toRing_443_, 10);
v_intCastFn_x3f_465_ = lean_ctor_get(v_toRing_443_, 11);
v_natCastFn_x3f_466_ = lean_ctor_get(v_toRing_443_, 12);
v_natSMulFn_x3f_467_ = lean_ctor_get(v_toRing_443_, 13);
v_intSMulFn_x3f_468_ = lean_ctor_get(v_toRing_443_, 14);
v_one_x3f_469_ = lean_ctor_get(v_toRing_443_, 15);
v_isSharedCheck_480_ = !lean_is_exclusive(v_toRing_443_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_toRing_443_, 6);
lean_dec(v_unused_481_);
v___x_471_ = v_toRing_443_;
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_one_x3f_469_);
lean_inc(v_intSMulFn_x3f_468_);
lean_inc(v_natSMulFn_x3f_467_);
lean_inc(v_natCastFn_x3f_466_);
lean_inc(v_intCastFn_x3f_465_);
lean_inc(v_powFn_x3f_464_);
lean_inc(v_negFn_x3f_463_);
lean_inc(v_subFn_x3f_462_);
lean_inc(v_mulFn_x3f_461_);
lean_inc(v_charInst_x3f_460_);
lean_inc(v_semiringInst_459_);
lean_inc(v_ringInst_458_);
lean_inc(v_u_457_);
lean_inc(v_type_456_);
lean_inc(v_id_455_);
lean_dec(v_toRing_443_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_a_441_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 6, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_id_455_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_type_456_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_u_457_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_ringInst_458_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_semiringInst_459_);
lean_ctor_set(v_reuseFailAlloc_479_, 5, v_charInst_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 6, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 7, v_mulFn_x3f_461_);
lean_ctor_set(v_reuseFailAlloc_479_, 8, v_subFn_x3f_462_);
lean_ctor_set(v_reuseFailAlloc_479_, 9, v_negFn_x3f_463_);
lean_ctor_set(v_reuseFailAlloc_479_, 10, v_powFn_x3f_464_);
lean_ctor_set(v_reuseFailAlloc_479_, 11, v_intCastFn_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_479_, 12, v_natCastFn_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_479_, 13, v_natSMulFn_x3f_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 14, v_intSMulFn_x3f_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 15, v_one_x3f_469_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_475_);
v___x_477_ = v___x_453_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_invFn_x3f_444_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_divFn_x3f_445_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_semiringId_x3f_446_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_commSemiringInst_447_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_commRingInst_448_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_noZeroDivInst_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_fieldInst_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_powIdentityInst_x3f_451_);
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
lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_558_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_558_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_558_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_558_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_toRing_519_; lean_object* v_addFn_x3f_520_; 
v_toRing_519_ = lean_ctor_get(v_a_515_, 0);
lean_inc_ref(v_toRing_519_);
lean_dec(v_a_515_);
v_addFn_x3f_520_ = lean_ctor_get(v_toRing_519_, 6);
if (lean_obj_tag(v_addFn_x3f_520_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_523_; 
lean_inc_ref(v_addFn_x3f_520_);
lean_dec_ref(v_toRing_519_);
v_val_521_ = lean_ctor_get(v_addFn_x3f_520_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v_addFn_x3f_520_, 1);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v_val_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_val_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v_type_525_; lean_object* v_u_526_; lean_object* v_semiringInst_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_expectedInst_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_517_);
v_type_525_ = lean_ctor_get(v_toRing_519_, 1);
lean_inc_ref_n(v_type_525_, 3);
v_u_526_ = lean_ctor_get(v_toRing_519_, 2);
lean_inc_n(v_u_526_, 2);
v_semiringInst_527_ = lean_ctor_get(v_toRing_519_, 4);
lean_inc_ref(v_semiringInst_527_);
lean_dec_ref(v_toRing_519_);
v___x_528_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_529_ = lean_box(0);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v_u_526_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc_ref(v___x_530_);
v___x_531_ = l_Lean_mkConst(v___x_528_, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6));
v___x_533_ = l_Lean_mkConst(v___x_532_, v___x_530_);
v___x_534_ = l_Lean_mkAppB(v___x_533_, v_type_525_, v_semiringInst_527_);
v_expectedInst_535_ = l_Lean_mkAppB(v___x_531_, v_type_525_, v___x_534_);
v___x_536_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8));
v___x_537_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10));
v___x_538_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_525_, v_u_526_, v___x_536_, v___x_537_, v_expectedInst_535_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_n(v_a_539_, 2);
lean_dec_ref_known(v___x_538_, 1);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_540_, 0, v_a_539_);
v___x_541_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_540_, v___y_502_, v___y_508_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_a_539_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_539_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_539_);
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_514_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_514_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_502_ = stack[0].m_obj;
lean_object* v___y_503_ = stack[1].m_obj;
lean_object* v___y_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v___y_511_ = stack[9].m_obj;
lean_object* v___y_512_ = stack[10].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_580_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_581_, lean_object* v_u_582_, lean_object* v_instDeclName_583_, lean_object* v_declName_584_, lean_object* v_expectedInst_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v_u_582_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc_ref(v___x_599_);
v___x_600_ = l_Lean_mkConst(v_instDeclName_583_, v___x_599_);
lean_inc_ref(v_type_581_);
v___x_601_ = l_Lean_Expr_app___override(v___x_600_, v_type_581_);
v___x_602_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_601_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc_n(v_a_603_, 2);
lean_dec_ref_known(v___x_602_, 1);
lean_inc(v_declName_584_);
v___x_604_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_584_, v_a_603_, v_expectedInst_585_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref_known(v___x_604_, 1);
v___x_605_ = l_Lean_mkConst(v_declName_584_, v___x_599_);
v___x_606_ = l_Lean_mkAppB(v___x_605_, v_type_581_, v_a_603_);
v___x_607_ = l_Lean_Meta_Sym_canon(v___x_606_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_Sym_shareCommon(v_a_608_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_609_;
}
else
{
return v___x_607_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_603_);
lean_dec_ref_known(v___x_599_, 2);
lean_dec(v_declName_584_);
lean_dec_ref(v_type_581_);
v_a_610_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_604_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_604_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_599_, 2);
lean_dec_ref(v_expectedInst_585_);
lean_dec(v_declName_584_);
lean_dec_ref(v_type_581_);
return v___x_602_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_581_ = stack[0].m_obj;
lean_object* v_u_582_ = stack[1].m_obj;
lean_object* v_instDeclName_583_ = stack[2].m_obj;
lean_object* v_declName_584_ = stack[3].m_obj;
lean_object* v_expectedInst_585_ = stack[4].m_obj;
lean_object* v___y_586_ = stack[5].m_obj;
lean_object* v___y_587_ = stack[6].m_obj;
lean_object* v___y_588_ = stack[7].m_obj;
lean_object* v___y_589_ = stack[8].m_obj;
lean_object* v___y_590_ = stack[9].m_obj;
lean_object* v___y_591_ = stack[10].m_obj;
lean_object* v___y_592_ = stack[11].m_obj;
lean_object* v___y_593_ = stack[12].m_obj;
lean_object* v___y_594_ = stack[13].m_obj;
lean_object* v___y_595_ = stack[14].m_obj;
lean_object* v___y_596_ = stack[15].m_obj;
lean_object* v_res_618_;
v_res_618_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_581_, v_u_582_, v_instDeclName_583_, v_declName_584_, v_expectedInst_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_619_ = _args[0];
lean_object* v_u_620_ = _args[1];
lean_object* v_instDeclName_621_ = _args[2];
lean_object* v_declName_622_ = _args[3];
lean_object* v_expectedInst_623_ = _args[4];
lean_object* v___y_624_ = _args[5];
lean_object* v___y_625_ = _args[6];
lean_object* v___y_626_ = _args[7];
lean_object* v___y_627_ = _args[8];
lean_object* v___y_628_ = _args[9];
lean_object* v___y_629_ = _args[10];
lean_object* v___y_630_ = _args[11];
lean_object* v___y_631_ = _args[12];
lean_object* v___y_632_ = _args[13];
lean_object* v___y_633_ = _args[14];
lean_object* v___y_634_ = _args[15];
lean_object* v___y_635_ = _args[16];
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_619_, v_u_620_, v_instDeclName_621_, v_declName_622_, v_expectedInst_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_637_, lean_object* v_s_638_){
_start:
{
lean_object* v_toRing_639_; lean_object* v_invFn_x3f_640_; lean_object* v_divFn_x3f_641_; lean_object* v_semiringId_x3f_642_; lean_object* v_commSemiringInst_643_; lean_object* v_commRingInst_644_; lean_object* v_noZeroDivInst_x3f_645_; lean_object* v_fieldInst_x3f_646_; lean_object* v_powIdentityInst_x3f_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_678_; 
v_toRing_639_ = lean_ctor_get(v_s_638_, 0);
v_invFn_x3f_640_ = lean_ctor_get(v_s_638_, 1);
v_divFn_x3f_641_ = lean_ctor_get(v_s_638_, 2);
v_semiringId_x3f_642_ = lean_ctor_get(v_s_638_, 3);
v_commSemiringInst_643_ = lean_ctor_get(v_s_638_, 4);
v_commRingInst_644_ = lean_ctor_get(v_s_638_, 5);
v_noZeroDivInst_x3f_645_ = lean_ctor_get(v_s_638_, 6);
v_fieldInst_x3f_646_ = lean_ctor_get(v_s_638_, 7);
v_powIdentityInst_x3f_647_ = lean_ctor_get(v_s_638_, 8);
v_isSharedCheck_678_ = !lean_is_exclusive(v_s_638_);
if (v_isSharedCheck_678_ == 0)
{
v___x_649_ = v_s_638_;
v_isShared_650_ = v_isSharedCheck_678_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_powIdentityInst_x3f_647_);
lean_inc(v_fieldInst_x3f_646_);
lean_inc(v_noZeroDivInst_x3f_645_);
lean_inc(v_commRingInst_644_);
lean_inc(v_commSemiringInst_643_);
lean_inc(v_semiringId_x3f_642_);
lean_inc(v_divFn_x3f_641_);
lean_inc(v_invFn_x3f_640_);
lean_inc(v_toRing_639_);
lean_dec(v_s_638_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_678_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_id_651_; lean_object* v_type_652_; lean_object* v_u_653_; lean_object* v_ringInst_654_; lean_object* v_semiringInst_655_; lean_object* v_charInst_x3f_656_; lean_object* v_addFn_x3f_657_; lean_object* v_mulFn_x3f_658_; lean_object* v_subFn_x3f_659_; lean_object* v_powFn_x3f_660_; lean_object* v_intCastFn_x3f_661_; lean_object* v_natCastFn_x3f_662_; lean_object* v_natSMulFn_x3f_663_; lean_object* v_intSMulFn_x3f_664_; lean_object* v_one_x3f_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_676_; 
v_id_651_ = lean_ctor_get(v_toRing_639_, 0);
v_type_652_ = lean_ctor_get(v_toRing_639_, 1);
v_u_653_ = lean_ctor_get(v_toRing_639_, 2);
v_ringInst_654_ = lean_ctor_get(v_toRing_639_, 3);
v_semiringInst_655_ = lean_ctor_get(v_toRing_639_, 4);
v_charInst_x3f_656_ = lean_ctor_get(v_toRing_639_, 5);
v_addFn_x3f_657_ = lean_ctor_get(v_toRing_639_, 6);
v_mulFn_x3f_658_ = lean_ctor_get(v_toRing_639_, 7);
v_subFn_x3f_659_ = lean_ctor_get(v_toRing_639_, 8);
v_powFn_x3f_660_ = lean_ctor_get(v_toRing_639_, 10);
v_intCastFn_x3f_661_ = lean_ctor_get(v_toRing_639_, 11);
v_natCastFn_x3f_662_ = lean_ctor_get(v_toRing_639_, 12);
v_natSMulFn_x3f_663_ = lean_ctor_get(v_toRing_639_, 13);
v_intSMulFn_x3f_664_ = lean_ctor_get(v_toRing_639_, 14);
v_one_x3f_665_ = lean_ctor_get(v_toRing_639_, 15);
v_isSharedCheck_676_ = !lean_is_exclusive(v_toRing_639_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_toRing_639_, 9);
lean_dec(v_unused_677_);
v___x_667_ = v_toRing_639_;
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_one_x3f_665_);
lean_inc(v_intSMulFn_x3f_664_);
lean_inc(v_natSMulFn_x3f_663_);
lean_inc(v_natCastFn_x3f_662_);
lean_inc(v_intCastFn_x3f_661_);
lean_inc(v_powFn_x3f_660_);
lean_inc(v_subFn_x3f_659_);
lean_inc(v_mulFn_x3f_658_);
lean_inc(v_addFn_x3f_657_);
lean_inc(v_charInst_x3f_656_);
lean_inc(v_semiringInst_655_);
lean_inc(v_ringInst_654_);
lean_inc(v_u_653_);
lean_inc(v_type_652_);
lean_inc(v_id_651_);
lean_dec(v_toRing_639_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_a_637_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 9, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_id_651_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_type_652_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_u_653_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_ringInst_654_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_semiringInst_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v_charInst_x3f_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_addFn_x3f_657_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v_mulFn_x3f_658_);
lean_ctor_set(v_reuseFailAlloc_675_, 8, v_subFn_x3f_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 9, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 10, v_powFn_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 11, v_intCastFn_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 12, v_natCastFn_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_675_, 13, v_natSMulFn_x3f_663_);
lean_ctor_set(v_reuseFailAlloc_675_, 14, v_intSMulFn_x3f_664_);
lean_ctor_set(v_reuseFailAlloc_675_, 15, v_one_x3f_665_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_671_);
v___x_673_ = v___x_649_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_invFn_x3f_640_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_divFn_x3f_641_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_semiringId_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_commSemiringInst_643_);
lean_ctor_set(v_reuseFailAlloc_674_, 5, v_commRingInst_644_);
lean_ctor_set(v_reuseFailAlloc_674_, 6, v_noZeroDivInst_x3f_645_);
lean_ctor_set(v_reuseFailAlloc_674_, 7, v_fieldInst_x3f_646_);
lean_ctor_set(v_reuseFailAlloc_674_, 8, v_powIdentityInst_x3f_647_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_746_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_746_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_746_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_746_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_toRing_710_; lean_object* v_negFn_x3f_711_; 
v_toRing_710_ = lean_ctor_get(v_a_706_, 0);
lean_inc_ref(v_toRing_710_);
lean_dec(v_a_706_);
v_negFn_x3f_711_ = lean_ctor_get(v_toRing_710_, 9);
if (lean_obj_tag(v_negFn_x3f_711_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_714_; 
lean_inc_ref(v_negFn_x3f_711_);
lean_dec_ref(v_toRing_710_);
v_val_712_ = lean_ctor_get(v_negFn_x3f_711_, 0);
lean_inc(v_val_712_);
lean_dec_ref_known(v_negFn_x3f_711_, 1);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_val_712_);
v___x_714_ = v___x_708_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_val_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v_type_716_; lean_object* v_u_717_; lean_object* v_ringInst_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_expectedInst_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_del_object(v___x_708_);
v_type_716_ = lean_ctor_get(v_toRing_710_, 1);
lean_inc_ref_n(v_type_716_, 2);
v_u_717_ = lean_ctor_get(v_toRing_710_, 2);
lean_inc_n(v_u_717_, 2);
v_ringInst_718_ = lean_ctor_get(v_toRing_710_, 3);
lean_inc_ref(v_ringInst_718_);
lean_dec_ref(v_toRing_710_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2));
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v_u_717_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_mkConst(v___x_719_, v___x_721_);
v_expectedInst_723_ = l_Lean_mkAppB(v___x_722_, v_type_716_, v_ringInst_718_);
v___x_724_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_725_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_726_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_716_, v_u_717_, v___x_724_, v___x_725_, v_expectedInst_723_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___f_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_n(v_a_727_, 2);
lean_dec_ref_known(v___x_726_, 1);
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_728_, 0, v_a_727_);
v___x_729_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_728_, v___y_693_, v___y_699_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_737_);
v___x_731_ = v___x_729_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_dec(v___x_729_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v_a_727_);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_727_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_727_);
v_a_738_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_729_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_729_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_705_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_705_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_693_ = stack[0].m_obj;
lean_object* v___y_694_ = stack[1].m_obj;
lean_object* v___y_695_ = stack[2].m_obj;
lean_object* v___y_696_ = stack[3].m_obj;
lean_object* v___y_697_ = stack[4].m_obj;
lean_object* v___y_698_ = stack[5].m_obj;
lean_object* v___y_699_ = stack[6].m_obj;
lean_object* v___y_700_ = stack[7].m_obj;
lean_object* v___y_701_ = stack[8].m_obj;
lean_object* v___y_702_ = stack[9].m_obj;
lean_object* v___y_703_ = stack[10].m_obj;
lean_object* v_res_755_;
v_res_755_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_768_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_nat_to_int(v___x_776_);
return v___x_777_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_857_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_857_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_857_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_857_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_toRing_801_; lean_object* v_type_802_; lean_object* v_u_803_; lean_object* v_semiringInst_804_; lean_object* v___x_805_; lean_object* v_n_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_ofNatInst_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_toRing_801_ = lean_ctor_get(v_a_797_, 0);
lean_inc_ref(v_toRing_801_);
lean_dec(v_a_797_);
v_type_802_ = lean_ctor_get(v_toRing_801_, 1);
lean_inc_ref_n(v_type_802_, 2);
v_u_803_ = lean_ctor_get(v_toRing_801_, 2);
lean_inc(v_u_803_);
v_semiringInst_804_ = lean_ctor_get(v_toRing_801_, 4);
lean_inc_ref(v_semiringInst_804_);
lean_dec_ref(v_toRing_801_);
v___x_805_ = lean_nat_abs(v_k_783_);
v_n_806_ = l_Lean_mkRawNatLit(v___x_805_);
v___x_807_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_809_, 0, v_u_803_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
lean_inc_ref(v___x_809_);
v___x_841_ = l_Lean_mkConst(v___x_807_, v___x_809_);
lean_inc_ref(v_n_806_);
v___x_842_ = l_Lean_mkAppB(v___x_841_, v_type_802_, v_n_806_);
v___x_843_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_842_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v_a_844_) == 1)
{
lean_object* v_val_845_; 
lean_dec_ref(v_semiringInst_804_);
v_val_845_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v_a_844_, 1);
v_ofNatInst_811_ = v_val_845_;
v___y_812_ = v___y_784_;
v___y_813_ = v___y_785_;
v___y_814_ = v___y_786_;
v___y_815_ = v___y_787_;
v___y_816_ = v___y_788_;
v___y_817_ = v___y_789_;
v___y_818_ = v___y_790_;
v___y_819_ = v___y_791_;
v___y_820_ = v___y_792_;
v___y_821_ = v___y_793_;
v___y_822_ = v___y_794_;
goto v___jp_810_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v_a_844_);
v___x_846_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5));
lean_inc_ref(v___x_809_);
v___x_847_ = l_Lean_mkConst(v___x_846_, v___x_809_);
lean_inc_ref(v_n_806_);
lean_inc_ref(v_type_802_);
v___x_848_ = l_Lean_mkApp3(v___x_847_, v_type_802_, v_semiringInst_804_, v_n_806_);
v_ofNatInst_811_ = v___x_848_;
v___y_812_ = v___y_784_;
v___y_813_ = v___y_785_;
v___y_814_ = v___y_786_;
v___y_815_ = v___y_787_;
v___y_816_ = v___y_788_;
v___y_817_ = v___y_789_;
v___y_818_ = v___y_790_;
v___y_819_ = v___y_791_;
v___y_820_ = v___y_792_;
v___y_821_ = v___y_793_;
v___y_822_ = v___y_794_;
goto v___jp_810_;
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref_known(v___x_809_, 2);
lean_dec_ref(v_n_806_);
lean_dec_ref(v_semiringInst_804_);
lean_dec_ref(v_type_802_);
lean_del_object(v___x_799_);
v_a_849_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_843_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_843_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
v___jp_810_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_e_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_823_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_824_ = l_Lean_mkConst(v___x_823_, v___x_809_);
v_e_825_ = l_Lean_mkApp3(v___x_824_, v_type_802_, v_n_806_, v_ofNatInst_811_);
v___x_826_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_827_ = lean_int_dec_lt(v_k_783_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_e_825_);
v___x_829_ = v___x_799_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_e_825_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v___x_831_; 
lean_del_object(v___x_799_);
v___x_831_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_840_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Expr_app___override(v_a_832_, v_e_825_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
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
lean_dec_ref(v_e_825_);
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_796_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_796_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_783_ = stack[0].m_obj;
lean_object* v___y_784_ = stack[1].m_obj;
lean_object* v___y_785_ = stack[2].m_obj;
lean_object* v___y_786_ = stack[3].m_obj;
lean_object* v___y_787_ = stack[4].m_obj;
lean_object* v___y_788_ = stack[5].m_obj;
lean_object* v___y_789_ = stack[6].m_obj;
lean_object* v___y_790_ = stack[7].m_obj;
lean_object* v___y_791_ = stack[8].m_obj;
lean_object* v___y_792_ = stack[9].m_obj;
lean_object* v___y_793_ = stack[10].m_obj;
lean_object* v___y_794_ = stack[11].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v_k_867_);
return v_res_880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_Level_ofNat(v___x_883_);
return v___x_884_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_891_, lean_object* v_type_892_, lean_object* v_semiringInst_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_908_ = lean_box(0);
lean_inc(v_u_891_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_u_891_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc_ref(v___x_909_);
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_907_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v_u_891_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
lean_inc_ref(v___x_911_);
v___x_912_ = l_Lean_mkConst(v___x_906_, v___x_911_);
v___x_913_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_892_, 2);
v___x_914_ = l_Lean_mkApp3(v___x_912_, v_type_892_, v___x_913_, v_type_892_);
v___x_915_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_914_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_inst_x27_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_n(v_a_916_, 2);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_918_ = l_Lean_mkConst(v___x_917_, v___x_909_);
lean_inc_ref(v_type_892_);
v_inst_x27_919_ = l_Lean_mkAppB(v___x_918_, v_type_892_, v_semiringInst_893_);
v___x_920_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_921_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_920_, v_a_916_, v_inst_x27_919_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref_known(v___x_921_, 1);
v___x_922_ = l_Lean_mkConst(v___x_920_, v___x_911_);
lean_inc_ref(v_type_892_);
v___x_923_ = l_Lean_mkApp4(v___x_922_, v_type_892_, v___x_913_, v_type_892_, v_a_916_);
v___x_924_ = l_Lean_Meta_Sym_canon(v___x_923_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = l_Lean_Meta_Sym_shareCommon(v_a_925_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_926_;
}
else
{
return v___x_924_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_a_916_);
lean_dec_ref_known(v___x_911_, 2);
lean_dec_ref(v_type_892_);
v_a_927_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_921_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_921_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_911_, 2);
lean_dec_ref_known(v___x_909_, 2);
lean_dec_ref(v_semiringInst_893_);
lean_dec_ref(v_type_892_);
return v___x_915_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_891_ = stack[0].m_obj;
lean_object* v_type_892_ = stack[1].m_obj;
lean_object* v_semiringInst_893_ = stack[2].m_obj;
lean_object* v___y_894_ = stack[3].m_obj;
lean_object* v___y_895_ = stack[4].m_obj;
lean_object* v___y_896_ = stack[5].m_obj;
lean_object* v___y_897_ = stack[6].m_obj;
lean_object* v___y_898_ = stack[7].m_obj;
lean_object* v___y_899_ = stack[8].m_obj;
lean_object* v___y_900_ = stack[9].m_obj;
lean_object* v___y_901_ = stack[10].m_obj;
lean_object* v___y_902_ = stack[11].m_obj;
lean_object* v___y_903_ = stack[12].m_obj;
lean_object* v___y_904_ = stack[13].m_obj;
lean_object* v_res_935_;
v_res_935_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_891_, v_type_892_, v_semiringInst_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
stack->m_obj
 = v_res_935_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_936_, lean_object* v_type_937_, lean_object* v_semiringInst_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_936_, v_type_937_, v_semiringInst_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_952_, lean_object* v_s_953_){
_start:
{
lean_object* v_toRing_954_; lean_object* v_invFn_x3f_955_; lean_object* v_divFn_x3f_956_; lean_object* v_semiringId_x3f_957_; lean_object* v_commSemiringInst_958_; lean_object* v_commRingInst_959_; lean_object* v_noZeroDivInst_x3f_960_; lean_object* v_fieldInst_x3f_961_; lean_object* v_powIdentityInst_x3f_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_993_; 
v_toRing_954_ = lean_ctor_get(v_s_953_, 0);
v_invFn_x3f_955_ = lean_ctor_get(v_s_953_, 1);
v_divFn_x3f_956_ = lean_ctor_get(v_s_953_, 2);
v_semiringId_x3f_957_ = lean_ctor_get(v_s_953_, 3);
v_commSemiringInst_958_ = lean_ctor_get(v_s_953_, 4);
v_commRingInst_959_ = lean_ctor_get(v_s_953_, 5);
v_noZeroDivInst_x3f_960_ = lean_ctor_get(v_s_953_, 6);
v_fieldInst_x3f_961_ = lean_ctor_get(v_s_953_, 7);
v_powIdentityInst_x3f_962_ = lean_ctor_get(v_s_953_, 8);
v_isSharedCheck_993_ = !lean_is_exclusive(v_s_953_);
if (v_isSharedCheck_993_ == 0)
{
v___x_964_ = v_s_953_;
v_isShared_965_ = v_isSharedCheck_993_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_powIdentityInst_x3f_962_);
lean_inc(v_fieldInst_x3f_961_);
lean_inc(v_noZeroDivInst_x3f_960_);
lean_inc(v_commRingInst_959_);
lean_inc(v_commSemiringInst_958_);
lean_inc(v_semiringId_x3f_957_);
lean_inc(v_divFn_x3f_956_);
lean_inc(v_invFn_x3f_955_);
lean_inc(v_toRing_954_);
lean_dec(v_s_953_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_993_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_id_966_; lean_object* v_type_967_; lean_object* v_u_968_; lean_object* v_ringInst_969_; lean_object* v_semiringInst_970_; lean_object* v_charInst_x3f_971_; lean_object* v_addFn_x3f_972_; lean_object* v_mulFn_x3f_973_; lean_object* v_subFn_x3f_974_; lean_object* v_negFn_x3f_975_; lean_object* v_intCastFn_x3f_976_; lean_object* v_natCastFn_x3f_977_; lean_object* v_natSMulFn_x3f_978_; lean_object* v_intSMulFn_x3f_979_; lean_object* v_one_x3f_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_991_; 
v_id_966_ = lean_ctor_get(v_toRing_954_, 0);
v_type_967_ = lean_ctor_get(v_toRing_954_, 1);
v_u_968_ = lean_ctor_get(v_toRing_954_, 2);
v_ringInst_969_ = lean_ctor_get(v_toRing_954_, 3);
v_semiringInst_970_ = lean_ctor_get(v_toRing_954_, 4);
v_charInst_x3f_971_ = lean_ctor_get(v_toRing_954_, 5);
v_addFn_x3f_972_ = lean_ctor_get(v_toRing_954_, 6);
v_mulFn_x3f_973_ = lean_ctor_get(v_toRing_954_, 7);
v_subFn_x3f_974_ = lean_ctor_get(v_toRing_954_, 8);
v_negFn_x3f_975_ = lean_ctor_get(v_toRing_954_, 9);
v_intCastFn_x3f_976_ = lean_ctor_get(v_toRing_954_, 11);
v_natCastFn_x3f_977_ = lean_ctor_get(v_toRing_954_, 12);
v_natSMulFn_x3f_978_ = lean_ctor_get(v_toRing_954_, 13);
v_intSMulFn_x3f_979_ = lean_ctor_get(v_toRing_954_, 14);
v_one_x3f_980_ = lean_ctor_get(v_toRing_954_, 15);
v_isSharedCheck_991_ = !lean_is_exclusive(v_toRing_954_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_toRing_954_, 10);
lean_dec(v_unused_992_);
v___x_982_ = v_toRing_954_;
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_one_x3f_980_);
lean_inc(v_intSMulFn_x3f_979_);
lean_inc(v_natSMulFn_x3f_978_);
lean_inc(v_natCastFn_x3f_977_);
lean_inc(v_intCastFn_x3f_976_);
lean_inc(v_negFn_x3f_975_);
lean_inc(v_subFn_x3f_974_);
lean_inc(v_mulFn_x3f_973_);
lean_inc(v_addFn_x3f_972_);
lean_inc(v_charInst_x3f_971_);
lean_inc(v_semiringInst_970_);
lean_inc(v_ringInst_969_);
lean_inc(v_u_968_);
lean_inc(v_type_967_);
lean_inc(v_id_966_);
lean_dec(v_toRing_954_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_a_952_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 10, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_id_966_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_type_967_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_u_968_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_ringInst_969_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_semiringInst_970_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v_charInst_x3f_971_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v_addFn_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_990_, 7, v_mulFn_x3f_973_);
lean_ctor_set(v_reuseFailAlloc_990_, 8, v_subFn_x3f_974_);
lean_ctor_set(v_reuseFailAlloc_990_, 9, v_negFn_x3f_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 10, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_990_, 11, v_intCastFn_x3f_976_);
lean_ctor_set(v_reuseFailAlloc_990_, 12, v_natCastFn_x3f_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 13, v_natSMulFn_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 14, v_intSMulFn_x3f_979_);
lean_ctor_set(v_reuseFailAlloc_990_, 15, v_one_x3f_980_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_988_ = v___x_964_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_invFn_x3f_955_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_divFn_x3f_956_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_semiringId_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_commSemiringInst_958_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_commRingInst_959_);
lean_ctor_set(v_reuseFailAlloc_989_, 6, v_noZeroDivInst_x3f_960_);
lean_ctor_set(v_reuseFailAlloc_989_, 7, v_fieldInst_x3f_961_);
lean_ctor_set(v_reuseFailAlloc_989_, 8, v_powIdentityInst_x3f_962_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1040_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_toRing_1011_; lean_object* v_powFn_x3f_1012_; 
v_toRing_1011_ = lean_ctor_get(v_a_1007_, 0);
lean_inc_ref(v_toRing_1011_);
lean_dec(v_a_1007_);
v_powFn_x3f_1012_ = lean_ctor_get(v_toRing_1011_, 10);
if (lean_obj_tag(v_powFn_x3f_1012_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; 
lean_inc_ref(v_powFn_x3f_1012_);
lean_dec_ref(v_toRing_1011_);
v_val_1013_ = lean_ctor_get(v_powFn_x3f_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_powFn_x3f_1012_, 1);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v_val_1013_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_val_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v_type_1017_; lean_object* v_u_1018_; lean_object* v_semiringInst_1019_; lean_object* v___x_1020_; 
lean_del_object(v___x_1009_);
v_type_1017_ = lean_ctor_get(v_toRing_1011_, 1);
lean_inc_ref(v_type_1017_);
v_u_1018_ = lean_ctor_get(v_toRing_1011_, 2);
lean_inc(v_u_1018_);
v_semiringInst_1019_ = lean_ctor_get(v_toRing_1011_, 4);
lean_inc_ref(v_semiringInst_1019_);
lean_dec_ref(v_toRing_1011_);
v___x_1020_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1018_, v_type_1017_, v_semiringInst_1019_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_n(v_a_1021_, 2);
lean_dec_ref_known(v___x_1020_, 1);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1022_, 0, v_a_1021_);
v___x_1023_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1022_, v___y_994_, v___y_1000_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v___x_1023_, 0);
lean_dec(v_unused_1031_);
v___x_1025_ = v___x_1023_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v___x_1023_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_a_1021_);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1021_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_1021_);
v_a_1032_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1006_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1006_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_994_ = stack[0].m_obj;
lean_object* v___y_995_ = stack[1].m_obj;
lean_object* v___y_996_ = stack[2].m_obj;
lean_object* v___y_997_ = stack[3].m_obj;
lean_object* v___y_998_ = stack[4].m_obj;
lean_object* v___y_999_ = stack[5].m_obj;
lean_object* v___y_1000_ = stack[6].m_obj;
lean_object* v___y_1001_ = stack[7].m_obj;
lean_object* v___y_1002_ = stack[8].m_obj;
lean_object* v___y_1003_ = stack[9].m_obj;
lean_object* v___y_1004_ = stack[10].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1062_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_x_1076_; lean_object* v_k_1077_; lean_object* v___y_1079_; lean_object* v_a_1080_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_x_1076_ = lean_ctor_get(v_pw_1063_, 0);
lean_inc(v_x_1076_);
v_k_1077_ = lean_ctor_get(v_pw_1063_, 1);
lean_inc(v_k_1077_);
lean_dec_ref(v_pw_1063_);
v___x_1094_ = l_Lean_instInhabitedExpr;
v___x_1095_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_1064_, v___y_1065_, v___y_1073_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1112_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_toRingState_1100_; lean_object* v_vars_1101_; lean_object* v_size_1102_; uint8_t v___x_1103_; 
v_toRingState_1100_ = lean_ctor_get(v_a_1096_, 0);
lean_inc_ref(v_toRingState_1100_);
lean_dec(v_a_1096_);
v_vars_1101_ = lean_ctor_get(v_toRingState_1100_, 0);
lean_inc_ref(v_vars_1101_);
lean_dec_ref(v_toRingState_1100_);
v_size_1102_ = lean_ctor_get(v_vars_1101_, 2);
v___x_1103_ = lean_nat_dec_lt(v_x_1076_, v_size_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec_ref(v_vars_1101_);
lean_dec(v_x_1076_);
v___x_1104_ = l_outOfBounds___redArg(v___x_1094_);
lean_inc(v___x_1104_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1104_);
v___x_1106_ = v___x_1098_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1079_ = v___x_1106_;
v_a_1080_ = v___x_1104_;
goto v___jp_1078_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1094_, v_vars_1101_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec_ref(v_vars_1101_);
lean_inc(v___x_1108_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1108_);
v___x_1110_ = v___x_1098_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v___y_1079_ = v___x_1110_;
v_a_1080_ = v___x_1108_;
goto v___jp_1078_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_k_1077_);
lean_dec(v_x_1076_);
v_a_1113_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1095_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1095_);
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
v___jp_1078_:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_dec_eq(v_k_1077_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec_ref(v___y_1079_);
v___x_1083_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = l_Lean_mkNatLit(v_k_1077_);
v___x_1089_ = l_Lean_mkAppB(v_a_1084_, v_a_1080_, v___x_1088_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_dec_ref(v_a_1080_);
lean_dec(v_k_1077_);
return v___x_1083_;
}
}
else
{
lean_dec_ref(v_a_1080_);
lean_dec(v_k_1077_);
return v___y_1079_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_pw_1063_ = stack[0].m_obj;
lean_object* v___y_1064_ = stack[1].m_obj;
lean_object* v___y_1065_ = stack[2].m_obj;
lean_object* v___y_1066_ = stack[3].m_obj;
lean_object* v___y_1067_ = stack[4].m_obj;
lean_object* v___y_1068_ = stack[5].m_obj;
lean_object* v___y_1069_ = stack[6].m_obj;
lean_object* v___y_1070_ = stack[7].m_obj;
lean_object* v___y_1071_ = stack[8].m_obj;
lean_object* v___y_1072_ = stack[9].m_obj;
lean_object* v___y_1073_ = stack[10].m_obj;
lean_object* v___y_1074_ = stack[11].m_obj;
lean_object* v_res_1121_;
v_res_1121_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_1136_, lean_object* v_s_1137_){
_start:
{
lean_object* v_toRing_1138_; lean_object* v_invFn_x3f_1139_; lean_object* v_divFn_x3f_1140_; lean_object* v_semiringId_x3f_1141_; lean_object* v_commSemiringInst_1142_; lean_object* v_commRingInst_1143_; lean_object* v_noZeroDivInst_x3f_1144_; lean_object* v_fieldInst_x3f_1145_; lean_object* v_powIdentityInst_x3f_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1177_; 
v_toRing_1138_ = lean_ctor_get(v_s_1137_, 0);
v_invFn_x3f_1139_ = lean_ctor_get(v_s_1137_, 1);
v_divFn_x3f_1140_ = lean_ctor_get(v_s_1137_, 2);
v_semiringId_x3f_1141_ = lean_ctor_get(v_s_1137_, 3);
v_commSemiringInst_1142_ = lean_ctor_get(v_s_1137_, 4);
v_commRingInst_1143_ = lean_ctor_get(v_s_1137_, 5);
v_noZeroDivInst_x3f_1144_ = lean_ctor_get(v_s_1137_, 6);
v_fieldInst_x3f_1145_ = lean_ctor_get(v_s_1137_, 7);
v_powIdentityInst_x3f_1146_ = lean_ctor_get(v_s_1137_, 8);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_s_1137_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1148_ = v_s_1137_;
v_isShared_1149_ = v_isSharedCheck_1177_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1146_);
lean_inc(v_fieldInst_x3f_1145_);
lean_inc(v_noZeroDivInst_x3f_1144_);
lean_inc(v_commRingInst_1143_);
lean_inc(v_commSemiringInst_1142_);
lean_inc(v_semiringId_x3f_1141_);
lean_inc(v_divFn_x3f_1140_);
lean_inc(v_invFn_x3f_1139_);
lean_inc(v_toRing_1138_);
lean_dec(v_s_1137_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1177_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_id_1150_; lean_object* v_type_1151_; lean_object* v_u_1152_; lean_object* v_ringInst_1153_; lean_object* v_semiringInst_1154_; lean_object* v_charInst_x3f_1155_; lean_object* v_addFn_x3f_1156_; lean_object* v_subFn_x3f_1157_; lean_object* v_negFn_x3f_1158_; lean_object* v_powFn_x3f_1159_; lean_object* v_intCastFn_x3f_1160_; lean_object* v_natCastFn_x3f_1161_; lean_object* v_natSMulFn_x3f_1162_; lean_object* v_intSMulFn_x3f_1163_; lean_object* v_one_x3f_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1175_; 
v_id_1150_ = lean_ctor_get(v_toRing_1138_, 0);
v_type_1151_ = lean_ctor_get(v_toRing_1138_, 1);
v_u_1152_ = lean_ctor_get(v_toRing_1138_, 2);
v_ringInst_1153_ = lean_ctor_get(v_toRing_1138_, 3);
v_semiringInst_1154_ = lean_ctor_get(v_toRing_1138_, 4);
v_charInst_x3f_1155_ = lean_ctor_get(v_toRing_1138_, 5);
v_addFn_x3f_1156_ = lean_ctor_get(v_toRing_1138_, 6);
v_subFn_x3f_1157_ = lean_ctor_get(v_toRing_1138_, 8);
v_negFn_x3f_1158_ = lean_ctor_get(v_toRing_1138_, 9);
v_powFn_x3f_1159_ = lean_ctor_get(v_toRing_1138_, 10);
v_intCastFn_x3f_1160_ = lean_ctor_get(v_toRing_1138_, 11);
v_natCastFn_x3f_1161_ = lean_ctor_get(v_toRing_1138_, 12);
v_natSMulFn_x3f_1162_ = lean_ctor_get(v_toRing_1138_, 13);
v_intSMulFn_x3f_1163_ = lean_ctor_get(v_toRing_1138_, 14);
v_one_x3f_1164_ = lean_ctor_get(v_toRing_1138_, 15);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_toRing_1138_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_toRing_1138_, 7);
lean_dec(v_unused_1176_);
v___x_1166_ = v_toRing_1138_;
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_one_x3f_1164_);
lean_inc(v_intSMulFn_x3f_1163_);
lean_inc(v_natSMulFn_x3f_1162_);
lean_inc(v_natCastFn_x3f_1161_);
lean_inc(v_intCastFn_x3f_1160_);
lean_inc(v_powFn_x3f_1159_);
lean_inc(v_negFn_x3f_1158_);
lean_inc(v_subFn_x3f_1157_);
lean_inc(v_addFn_x3f_1156_);
lean_inc(v_charInst_x3f_1155_);
lean_inc(v_semiringInst_1154_);
lean_inc(v_ringInst_1153_);
lean_inc(v_u_1152_);
lean_inc(v_type_1151_);
lean_inc(v_id_1150_);
lean_dec(v_toRing_1138_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1136_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 7, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_id_1150_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_type_1151_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_u_1152_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_ringInst_1153_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_semiringInst_1154_);
lean_ctor_set(v_reuseFailAlloc_1174_, 5, v_charInst_x3f_1155_);
lean_ctor_set(v_reuseFailAlloc_1174_, 6, v_addFn_x3f_1156_);
lean_ctor_set(v_reuseFailAlloc_1174_, 7, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 8, v_subFn_x3f_1157_);
lean_ctor_set(v_reuseFailAlloc_1174_, 9, v_negFn_x3f_1158_);
lean_ctor_set(v_reuseFailAlloc_1174_, 10, v_powFn_x3f_1159_);
lean_ctor_set(v_reuseFailAlloc_1174_, 11, v_intCastFn_x3f_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 12, v_natCastFn_x3f_1161_);
lean_ctor_set(v_reuseFailAlloc_1174_, 13, v_natSMulFn_x3f_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 14, v_intSMulFn_x3f_1163_);
lean_ctor_set(v_reuseFailAlloc_1174_, 15, v_one_x3f_1164_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1170_);
v___x_1172_ = v___x_1148_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_invFn_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_divFn_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_semiringId_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_commSemiringInst_1142_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_commRingInst_1143_);
lean_ctor_set(v_reuseFailAlloc_1173_, 6, v_noZeroDivInst_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1173_, 7, v_fieldInst_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1173_, 8, v_powIdentityInst_x3f_1146_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1245_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1245_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1245_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_toRing_1206_; lean_object* v_mulFn_x3f_1207_; 
v_toRing_1206_ = lean_ctor_get(v_a_1202_, 0);
lean_inc_ref(v_toRing_1206_);
lean_dec(v_a_1202_);
v_mulFn_x3f_1207_ = lean_ctor_get(v_toRing_1206_, 7);
if (lean_obj_tag(v_mulFn_x3f_1207_) == 1)
{
lean_object* v_val_1208_; lean_object* v___x_1210_; 
lean_inc_ref(v_mulFn_x3f_1207_);
lean_dec_ref(v_toRing_1206_);
v_val_1208_ = lean_ctor_get(v_mulFn_x3f_1207_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v_mulFn_x3f_1207_, 1);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_val_1208_);
v___x_1210_ = v___x_1204_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v_type_1212_; lean_object* v_u_1213_; lean_object* v_semiringInst_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_expectedInst_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_del_object(v___x_1204_);
v_type_1212_ = lean_ctor_get(v_toRing_1206_, 1);
lean_inc_ref_n(v_type_1212_, 3);
v_u_1213_ = lean_ctor_get(v_toRing_1206_, 2);
lean_inc_n(v_u_1213_, 2);
v_semiringInst_1214_ = lean_ctor_get(v_toRing_1206_, 4);
lean_inc_ref(v_semiringInst_1214_);
lean_dec_ref(v_toRing_1206_);
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_u_1213_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_inc_ref(v___x_1217_);
v___x_1218_ = l_Lean_mkConst(v___x_1215_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_1220_ = l_Lean_mkConst(v___x_1219_, v___x_1217_);
v___x_1221_ = l_Lean_mkAppB(v___x_1220_, v_type_1212_, v_semiringInst_1214_);
v_expectedInst_1222_ = l_Lean_mkAppB(v___x_1218_, v_type_1212_, v___x_1221_);
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_1224_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_1225_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1212_, v_u_1213_, v___x_1223_, v___x_1224_, v_expectedInst_1222_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_n(v_a_1226_, 2);
lean_dec_ref_known(v___x_1225_, 1);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1227_, 0, v_a_1226_);
v___x_1228_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1227_, v___y_1189_, v___y_1195_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_a_1226_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1226_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1226_);
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1201_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1201_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1189_ = stack[0].m_obj;
lean_object* v___y_1190_ = stack[1].m_obj;
lean_object* v___y_1191_ = stack[2].m_obj;
lean_object* v___y_1192_ = stack[3].m_obj;
lean_object* v___y_1193_ = stack[4].m_obj;
lean_object* v___y_1194_ = stack[5].m_obj;
lean_object* v___y_1195_ = stack[6].m_obj;
lean_object* v___y_1196_ = stack[7].m_obj;
lean_object* v___y_1197_ = stack[8].m_obj;
lean_object* v___y_1198_ = stack[9].m_obj;
lean_object* v___y_1199_ = stack[10].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1267_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_mn_1268_, lean_object* v_acc_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
if (lean_obj_tag(v_mn_1268_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_acc_1269_);
return v___x_1282_;
}
else
{
lean_object* v_p_1283_; lean_object* v_m_1284_; lean_object* v___x_1285_; 
v_p_1283_ = lean_ctor_get(v_mn_1268_, 0);
lean_inc_ref(v_p_1283_);
v_m_1284_ = lean_ctor_get(v_mn_1268_, 1);
lean_inc(v_m_1284_);
lean_dec_ref_known(v_mn_1268_, 2);
v___x_1285_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1283_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = l_Lean_mkAppB(v_a_1286_, v_acc_1269_, v_a_1288_);
v_mn_1268_ = v_m_1284_;
v_acc_1269_ = v___x_1289_;
goto _start;
}
else
{
lean_dec(v_a_1286_);
lean_dec(v_m_1284_);
lean_dec_ref(v_acc_1269_);
return v___x_1287_;
}
}
else
{
lean_dec(v_m_1284_);
lean_dec_ref(v_p_1283_);
lean_dec_ref(v_acc_1269_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_mn_1268_ = stack[0].m_obj;
lean_object* v_acc_1269_ = stack[1].m_obj;
lean_object* v___y_1270_ = stack[2].m_obj;
lean_object* v___y_1271_ = stack[3].m_obj;
lean_object* v___y_1272_ = stack[4].m_obj;
lean_object* v___y_1273_ = stack[5].m_obj;
lean_object* v___y_1274_ = stack[6].m_obj;
lean_object* v___y_1275_ = stack[7].m_obj;
lean_object* v___y_1276_ = stack[8].m_obj;
lean_object* v___y_1277_ = stack[9].m_obj;
lean_object* v___y_1278_ = stack[10].m_obj;
lean_object* v___y_1279_ = stack[11].m_obj;
lean_object* v___y_1280_ = stack[12].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_mn_1268_, v_acc_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_mn_1292_, lean_object* v_acc_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_mn_1292_, v_acc_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1306_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_to_int(v___x_1307_);
return v___x_1308_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_mn_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
if (lean_obj_tag(v_mn_1309_) == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1323_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1322_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1323_;
}
else
{
lean_object* v_p_1324_; lean_object* v_m_1325_; lean_object* v___x_1326_; 
v_p_1324_ = lean_ctor_get(v_mn_1309_, 0);
lean_inc_ref(v_p_1324_);
v_m_1325_ = lean_ctor_get(v_mn_1309_, 1);
lean_inc(v_m_1325_);
lean_dec_ref_known(v_mn_1309_, 2);
v___x_1326_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1324_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1325_, v_a_1327_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1328_;
}
else
{
lean_dec(v_m_1325_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mn_1309_ = stack[0].m_obj;
lean_object* v___y_1310_ = stack[1].m_obj;
lean_object* v___y_1311_ = stack[2].m_obj;
lean_object* v___y_1312_ = stack[3].m_obj;
lean_object* v___y_1313_ = stack[4].m_obj;
lean_object* v___y_1314_ = stack[5].m_obj;
lean_object* v___y_1315_ = stack[6].m_obj;
lean_object* v___y_1316_ = stack[7].m_obj;
lean_object* v___y_1317_ = stack[8].m_obj;
lean_object* v___y_1318_ = stack[9].m_obj;
lean_object* v___y_1319_ = stack[10].m_obj;
lean_object* v___y_1320_ = stack[11].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mn_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1343_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1344_, lean_object* v_mn_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1359_ = lean_int_dec_eq(v_k_1344_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1344_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = l_Lean_mkAppB(v_a_1361_, v_a_1363_, v_a_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_dec(v_a_1363_);
lean_dec(v_a_1361_);
return v___x_1364_;
}
}
else
{
lean_dec(v_a_1361_);
lean_dec(v_mn_1345_);
return v___x_1362_;
}
}
else
{
lean_dec(v_mn_1345_);
return v___x_1360_;
}
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
return v___x_1374_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1344_ = stack[0].m_obj;
lean_object* v_mn_1345_ = stack[1].m_obj;
lean_object* v___y_1346_ = stack[2].m_obj;
lean_object* v___y_1347_ = stack[3].m_obj;
lean_object* v___y_1348_ = stack[4].m_obj;
lean_object* v___y_1349_ = stack[5].m_obj;
lean_object* v___y_1350_ = stack[6].m_obj;
lean_object* v___y_1351_ = stack[7].m_obj;
lean_object* v___y_1352_ = stack[8].m_obj;
lean_object* v___y_1353_ = stack[9].m_obj;
lean_object* v___y_1354_ = stack[10].m_obj;
lean_object* v___y_1355_ = stack[11].m_obj;
lean_object* v___y_1356_ = stack[12].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1344_, v_mn_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1376_, lean_object* v_mn_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1376_, v_mn_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
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
lean_dec(v_k_1376_);
return v_res_1390_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1391_, lean_object* v_acc_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
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
v___x_1409_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1410_ = lean_int_dec_eq(v_k_1405_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_del_object(v___x_1407_);
v___x_1411_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1405_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
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
v___x_1430_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1427_, v_v_1428_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1391_ = stack[0].m_obj;
lean_object* v_acc_1392_ = stack[1].m_obj;
lean_object* v___y_1393_ = stack[2].m_obj;
lean_object* v___y_1394_ = stack[3].m_obj;
lean_object* v___y_1395_ = stack[4].m_obj;
lean_object* v___y_1396_ = stack[5].m_obj;
lean_object* v___y_1397_ = stack[6].m_obj;
lean_object* v___y_1398_ = stack[7].m_obj;
lean_object* v___y_1399_ = stack[8].m_obj;
lean_object* v___y_1400_ = stack[9].m_obj;
lean_object* v___y_1401_ = stack[10].m_obj;
lean_object* v___y_1402_ = stack[11].m_obj;
lean_object* v___y_1403_ = stack[12].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1391_, v_acc_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
stack->m_obj
 = v_res_1436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1437_, lean_object* v_acc_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1437_, v_acc_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1451_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
if (lean_obj_tag(v_p_1452_) == 0)
{
lean_object* v_k_1465_; lean_object* v___x_1466_; 
v_k_1465_ = lean_ctor_get(v_p_1452_, 0);
lean_inc(v_k_1465_);
lean_dec_ref_known(v_p_1452_, 1);
v___x_1466_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1465_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v_k_1465_);
return v___x_1466_;
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_p_1469_; lean_object* v___x_1470_; 
v_k_1467_ = lean_ctor_get(v_p_1452_, 0);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v_p_1452_, 1);
lean_inc(v_v_1468_);
v_p_1469_ = lean_ctor_get(v_p_1452_, 2);
lean_inc_ref(v_p_1469_);
lean_dec_ref_known(v_p_1452_, 3);
v___x_1470_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1467_, v_v_1468_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v_k_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1469_, v_a_1471_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1472_;
}
else
{
lean_dec_ref(v_p_1469_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1452_ = stack[0].m_obj;
lean_object* v___y_1453_ = stack[1].m_obj;
lean_object* v___y_1454_ = stack[2].m_obj;
lean_object* v___y_1455_ = stack[3].m_obj;
lean_object* v___y_1456_ = stack[4].m_obj;
lean_object* v___y_1457_ = stack[5].m_obj;
lean_object* v___y_1458_ = stack[6].m_obj;
lean_object* v___y_1459_ = stack[7].m_obj;
lean_object* v___y_1460_ = stack[8].m_obj;
lean_object* v___y_1461_ = stack[9].m_obj;
lean_object* v___y_1462_ = stack[10].m_obj;
lean_object* v___y_1463_ = stack[11].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
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
lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1547_; 
v_ref_1500_ = lean_ctor_get(v___y_1497_, 2);
v___x_1501_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1547_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1547_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v_traceState_1507_; lean_object* v_env_1508_; lean_object* v_nextMacroScope_1509_; lean_object* v_ngen_1510_; lean_object* v_auxDeclNGen_1511_; lean_object* v_cache_1512_; lean_object* v_recordedDeps_1513_; lean_object* v_messages_1514_; lean_object* v_infoState_1515_; lean_object* v_snapshotTasks_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1546_; 
v___x_1506_ = lean_st_ref_take(v___y_1498_);
v_traceState_1507_ = lean_ctor_get(v___x_1506_, 4);
v_env_1508_ = lean_ctor_get(v___x_1506_, 0);
v_nextMacroScope_1509_ = lean_ctor_get(v___x_1506_, 1);
v_ngen_1510_ = lean_ctor_get(v___x_1506_, 2);
v_auxDeclNGen_1511_ = lean_ctor_get(v___x_1506_, 3);
v_cache_1512_ = lean_ctor_get(v___x_1506_, 5);
v_recordedDeps_1513_ = lean_ctor_get(v___x_1506_, 6);
v_messages_1514_ = lean_ctor_get(v___x_1506_, 7);
v_infoState_1515_ = lean_ctor_get(v___x_1506_, 8);
v_snapshotTasks_1516_ = lean_ctor_get(v___x_1506_, 9);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1518_ = v___x_1506_;
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snapshotTasks_1516_);
lean_inc(v_infoState_1515_);
lean_inc(v_messages_1514_);
lean_inc(v_recordedDeps_1513_);
lean_inc(v_cache_1512_);
lean_inc(v_traceState_1507_);
lean_inc(v_auxDeclNGen_1511_);
lean_inc(v_ngen_1510_);
lean_inc(v_nextMacroScope_1509_);
lean_inc(v_env_1508_);
lean_dec(v___x_1506_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint64_t v_tid_1520_; lean_object* v_traces_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_tid_1520_ = lean_ctor_get_uint64(v_traceState_1507_, sizeof(void*)*1);
v_traces_1521_ = lean_ctor_get(v_traceState_1507_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_traceState_1507_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1523_ = v_traceState_1507_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_traces_1521_);
lean_dec(v_traceState_1507_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; double v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1528_ = 0;
v___x_1529_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1530_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1530_, 0, v_cls_1493_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
lean_ctor_set_float(v___x_1530_, sizeof(void*)*3, v___x_1527_);
lean_ctor_set_float(v___x_1530_, sizeof(void*)*3 + 8, v___x_1527_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*3 + 16, v___x_1528_);
v___x_1531_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1532_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v_a_1502_);
lean_ctor_set(v___x_1532_, 2, v___x_1531_);
lean_inc(v_ref_1500_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_ref_1500_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_PersistentArray_push___redArg(v_traces_1521_, v___x_1533_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1534_);
v___x_1536_ = v___x_1523_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1534_);
lean_ctor_set_uint64(v_reuseFailAlloc_1544_, sizeof(void*)*1, v_tid_1520_);
v___x_1536_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1536_);
v___x_1538_ = v___x_1518_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_env_1508_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_nextMacroScope_1509_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_ngen_1510_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_auxDeclNGen_1511_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v_cache_1512_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_recordedDeps_1513_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_messages_1514_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_infoState_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 9, v_snapshotTasks_1516_);
v___x_1538_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_st_ref_put(v___y_1498_, v___x_1538_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1525_);
v___x_1541_ = v___x_1504_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1525_);
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
LEAN_EXPORT void l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1493_ = stack[0].m_obj;
lean_object* v_msg_1494_ = stack[1].m_obj;
lean_object* v___y_1495_ = stack[2].m_obj;
lean_object* v___y_1496_ = stack[3].m_obj;
lean_object* v___y_1497_ = stack[4].m_obj;
lean_object* v___y_1498_ = stack[5].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1556_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1572_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1573_ = l_Lean_Name_append(v___x_1572_, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1577_, v_a_1578_, v_a_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1816_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1816_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1816_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_unbox(v_a_1590_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v___x_1595_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_del_object(v___x_1592_);
lean_inc(v_a_1590_);
v___f_1599_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1599_, 0, v_a_1590_);
v___x_1600_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1807_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1807_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1807_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
if (lean_obj_tag(v_a_1601_) == 1)
{
lean_object* v_val_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_del_object(v___x_1603_);
v_val_1605_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1606_ = 0;
v___x_1607_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1607_, 0, v_val_1605_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*1, v___x_1606_);
lean_inc_ref(v_p_1577_);
v___x_1608_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1577_, v_a_1578_, v_a_1586_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = l_Lean_Meta_Sym_canon(v_a_1609_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_Meta_Sym_shareCommon(v_a_1611_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
lean_inc_ref(v_p_1577_);
v___x_1614_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1577_, v_a_1578_, v_a_1586_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = lean_unbox(v_a_1590_);
lean_dec(v_a_1590_);
v___x_1617_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1613_, v___x_1616_, v___x_1607_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1762_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1762_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1762_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
if (lean_obj_tag(v_a_1618_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1623_; 
lean_del_object(v___x_1620_);
v_val_1622_ = lean_ctor_get(v_a_1618_, 0);
lean_inc_n(v_val_1622_, 2);
lean_dec_ref_known(v_a_1618_, 1);
v___x_1623_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_val_1622_, v___x_1607_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1749_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1749_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1749_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
if (lean_obj_tag(v_a_1624_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1744_; 
lean_del_object(v___x_1626_);
v_val_1628_ = lean_ctor_get(v_a_1624_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1624_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1630_ = v_a_1624_;
v_isShared_1631_ = v_isSharedCheck_1744_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v_a_1624_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1744_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; 
lean_inc(v_val_1628_);
v___x_1632_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1628_, v___x_1607_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec_ref_known(v___x_1607_, 1);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1633_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc_n(v_a_1635_, 2);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1587_);
lean_inc_ref(v_a_1586_);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc(v_a_1578_);
v___x_1637_ = lean_grind_internalize(v_a_1635_, v_a_1615_, v___x_1636_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1718_; 
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v___x_1637_, 0);
lean_dec(v_unused_1719_);
v___x_1639_ = v___x_1637_;
v_isShared_1640_ = v_isSharedCheck_1718_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v___x_1637_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1718_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1635_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1709_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1709_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1709_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1577_, v_a_1642_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_del_object(v___x_1639_);
v___x_1656_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1657_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1656_, v___f_1599_, v_a_1578_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_toCold_1658_; lean_object* v_options_1659_; uint8_t v_hasTrace_1660_; 
lean_dec_ref_known(v___x_1657_, 1);
v_toCold_1658_ = lean_ctor_get(v_a_1586_, 0);
v_options_1659_ = lean_ctor_get(v_toCold_1658_, 2);
v_hasTrace_1660_ = lean_ctor_get_uint8(v_options_1659_, sizeof(void*)*1);
if (v_hasTrace_1660_ == 0)
{
lean_dec_ref(v_p_1577_);
goto v___jp_1646_;
}
else
{
lean_object* v_inheritedTraceOptions_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_inheritedTraceOptions_1661_ = lean_ctor_get(v_toCold_1658_, 11);
v___x_1662_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1663_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1661_, v_options_1659_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_p_1577_);
goto v___jp_1646_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1577_, v_a_1578_, v_a_1586_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
lean_inc(v_a_1642_);
v___x_1667_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1642_, v_a_1578_, v_a_1586_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1666_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1668_);
v___x_1672_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1662_, v___x_1671_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec_ref_known(v___x_1672_, 1);
goto v___jp_1646_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1666_);
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
v_a_1681_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1667_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1667_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
v_a_1689_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1665_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1665_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec_ref(v_p_1577_);
v_a_1697_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1657_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1657_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v___x_1705_ = lean_box(0);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1705_);
v___x_1707_ = v___x_1639_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
v___jp_1646_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_val_1628_);
lean_ctor_set(v___x_1647_, 1, v_a_1642_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_val_1622_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1648_);
v___x_1650_ = v___x_1630_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1650_);
v___x_1652_ = v___x_1644_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_del_object(v___x_1639_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1710_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1641_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1641_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1635_);
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1720_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1637_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1637_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec(v_a_1615_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1728_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1634_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1634_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1630_);
lean_dec(v_val_1628_);
lean_dec(v_val_1622_);
lean_dec(v_a_1615_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1736_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1632_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1632_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_a_1624_);
lean_dec(v_val_1622_);
lean_dec(v_a_1615_);
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v___x_1745_ = lean_box(0);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1745_);
v___x_1747_ = v___x_1626_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_val_1622_);
lean_dec(v_a_1615_);
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1750_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1623_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1623_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v___x_1758_ = lean_box(0);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1758_);
v___x_1760_ = v___x_1620_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1615_);
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v_p_1577_);
v_a_1763_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1617_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1617_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1613_);
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v_a_1771_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1614_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1614_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v_a_1779_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1612_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1612_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v_a_1787_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1610_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1610_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref_known(v___x_1607_, 1);
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v_a_1795_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1608_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1608_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec(v_a_1601_);
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v___x_1803_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1803_);
v___x_1805_ = v___x_1603_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v___f_1599_);
lean_dec(v_a_1590_);
lean_dec_ref(v_p_1577_);
v_a_1808_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1600_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1600_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_p_1577_);
v_a_1817_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1589_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1589_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_normCommRing_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_a_1579_ = stack[2].m_obj;
lean_object* v_a_1580_ = stack[3].m_obj;
lean_object* v_a_1581_ = stack[4].m_obj;
lean_object* v_a_1582_ = stack[5].m_obj;
lean_object* v_a_1583_ = stack[6].m_obj;
lean_object* v_a_1584_ = stack[7].m_obj;
lean_object* v_a_1585_ = stack[8].m_obj;
lean_object* v_a_1586_ = stack[9].m_obj;
lean_object* v_a_1587_ = stack[10].m_obj;
lean_object* v_res_1825_;
v_res_1825_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
stack->m_obj
 = v_res_1825_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
return v_res_1838_;
}
}
lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1839_, v_msg_1840_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1839_ = stack[0].m_obj;
lean_object* v_msg_1840_ = stack[1].m_obj;
lean_object* v___y_1841_ = stack[2].m_obj;
lean_object* v___y_1842_ = stack[3].m_obj;
lean_object* v___y_1843_ = stack[4].m_obj;
lean_object* v___y_1844_ = stack[5].m_obj;
lean_object* v___y_1845_ = stack[6].m_obj;
lean_object* v___y_1846_ = stack[7].m_obj;
lean_object* v___y_1847_ = stack[8].m_obj;
lean_object* v___y_1848_ = stack[9].m_obj;
lean_object* v___y_1849_ = stack[10].m_obj;
lean_object* v___y_1850_ = stack[11].m_obj;
lean_object* v___y_1851_ = stack[12].m_obj;
lean_object* v_res_1854_;
v_res_1854_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1839_, v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1855_, v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1869_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1871_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1871_ = stack[1].m_obj;
lean_object* v___y_1872_ = stack[2].m_obj;
lean_object* v___y_1873_ = stack[3].m_obj;
lean_object* v___y_1874_ = stack[4].m_obj;
lean_object* v___y_1875_ = stack[5].m_obj;
lean_object* v___y_1876_ = stack[6].m_obj;
lean_object* v___y_1877_ = stack[7].m_obj;
lean_object* v___y_1878_ = stack[8].m_obj;
lean_object* v___y_1879_ = stack[9].m_obj;
lean_object* v___y_1880_ = stack[10].m_obj;
lean_object* v___y_1881_ = stack[11].m_obj;
lean_object* v___y_1882_ = stack[12].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_box(0), v_msg_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1886_, v_msg_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1900_;
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
