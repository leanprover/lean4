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
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_31_ = l_Lean_Expr_isAppOf(v_a_18_, v___x_30_);
lean_dec(v_a_18_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_33_ = l_Lean_Expr_isAppOf(v_a_20_, v___x_32_);
lean_dec(v_a_20_);
if (v___x_33_ == 0)
{
lean_del_object(v___x_22_);
v_p_11_ = v_p_16_;
goto _start;
}
else
{
goto v___jp_24_;
}
}
else
{
lean_dec(v_a_20_);
goto v___jp_24_;
}
v___jp_24_:
{
uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_25_ = 1;
v___x_26_ = lean_box(v___x_25_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_26_);
v___x_28_ = v___x_22_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_187_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_a_195_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_196_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_194_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_194_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg___boxed(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_a_225_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(uint8_t v_a_237_, lean_object* v_s_238_){
_start:
{
lean_object* v_vars_239_; lean_object* v_varMap_240_; lean_object* v_varsHistory_241_; lean_object* v_natToIntMap_242_; lean_object* v_natDef_243_; lean_object* v_dvds_244_; lean_object* v_lowers_245_; lean_object* v_uppers_246_; lean_object* v_diseqs_247_; lean_object* v_elimEqs_248_; lean_object* v_active_249_; lean_object* v_elimStack_250_; lean_object* v_occurs_251_; lean_object* v_assignment_252_; lean_object* v_nextCnstrId_253_; uint8_t v_caseSplits_254_; lean_object* v_steps_255_; lean_object* v_penalties_256_; lean_object* v_numReorderRequests_257_; lean_object* v_conflict_x3f_258_; lean_object* v_diseqSplits_259_; lean_object* v_divMod_260_; lean_object* v_nonlinearOccs_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_vars_239_ = lean_ctor_get(v_s_238_, 0);
v_varMap_240_ = lean_ctor_get(v_s_238_, 1);
v_varsHistory_241_ = lean_ctor_get(v_s_238_, 2);
v_natToIntMap_242_ = lean_ctor_get(v_s_238_, 3);
v_natDef_243_ = lean_ctor_get(v_s_238_, 4);
v_dvds_244_ = lean_ctor_get(v_s_238_, 5);
v_lowers_245_ = lean_ctor_get(v_s_238_, 6);
v_uppers_246_ = lean_ctor_get(v_s_238_, 7);
v_diseqs_247_ = lean_ctor_get(v_s_238_, 8);
v_elimEqs_248_ = lean_ctor_get(v_s_238_, 9);
v_active_249_ = lean_ctor_get(v_s_238_, 10);
v_elimStack_250_ = lean_ctor_get(v_s_238_, 11);
v_occurs_251_ = lean_ctor_get(v_s_238_, 12);
v_assignment_252_ = lean_ctor_get(v_s_238_, 13);
v_nextCnstrId_253_ = lean_ctor_get(v_s_238_, 14);
v_caseSplits_254_ = lean_ctor_get_uint8(v_s_238_, sizeof(void*)*22);
v_steps_255_ = lean_ctor_get(v_s_238_, 15);
v_penalties_256_ = lean_ctor_get(v_s_238_, 16);
v_numReorderRequests_257_ = lean_ctor_get(v_s_238_, 17);
v_conflict_x3f_258_ = lean_ctor_get(v_s_238_, 18);
v_diseqSplits_259_ = lean_ctor_get(v_s_238_, 19);
v_divMod_260_ = lean_ctor_get(v_s_238_, 20);
v_nonlinearOccs_261_ = lean_ctor_get(v_s_238_, 21);
v_isSharedCheck_268_ = !lean_is_exclusive(v_s_238_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v_s_238_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_nonlinearOccs_261_);
lean_inc(v_divMod_260_);
lean_inc(v_diseqSplits_259_);
lean_inc(v_conflict_x3f_258_);
lean_inc(v_numReorderRequests_257_);
lean_inc(v_penalties_256_);
lean_inc(v_steps_255_);
lean_inc(v_nextCnstrId_253_);
lean_inc(v_assignment_252_);
lean_inc(v_occurs_251_);
lean_inc(v_elimStack_250_);
lean_inc(v_active_249_);
lean_inc(v_elimEqs_248_);
lean_inc(v_diseqs_247_);
lean_inc(v_uppers_246_);
lean_inc(v_lowers_245_);
lean_inc(v_dvds_244_);
lean_inc(v_natDef_243_);
lean_inc(v_natToIntMap_242_);
lean_inc(v_varsHistory_241_);
lean_inc(v_varMap_240_);
lean_inc(v_vars_239_);
lean_dec(v_s_238_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_vars_239_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_varMap_240_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_varsHistory_241_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_natToIntMap_242_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_natDef_243_);
lean_ctor_set(v_reuseFailAlloc_267_, 5, v_dvds_244_);
lean_ctor_set(v_reuseFailAlloc_267_, 6, v_lowers_245_);
lean_ctor_set(v_reuseFailAlloc_267_, 7, v_uppers_246_);
lean_ctor_set(v_reuseFailAlloc_267_, 8, v_diseqs_247_);
lean_ctor_set(v_reuseFailAlloc_267_, 9, v_elimEqs_248_);
lean_ctor_set(v_reuseFailAlloc_267_, 10, v_active_249_);
lean_ctor_set(v_reuseFailAlloc_267_, 11, v_elimStack_250_);
lean_ctor_set(v_reuseFailAlloc_267_, 12, v_occurs_251_);
lean_ctor_set(v_reuseFailAlloc_267_, 13, v_assignment_252_);
lean_ctor_set(v_reuseFailAlloc_267_, 14, v_nextCnstrId_253_);
lean_ctor_set(v_reuseFailAlloc_267_, 15, v_steps_255_);
lean_ctor_set(v_reuseFailAlloc_267_, 16, v_penalties_256_);
lean_ctor_set(v_reuseFailAlloc_267_, 17, v_numReorderRequests_257_);
lean_ctor_set(v_reuseFailAlloc_267_, 18, v_conflict_x3f_258_);
lean_ctor_set(v_reuseFailAlloc_267_, 19, v_diseqSplits_259_);
lean_ctor_set(v_reuseFailAlloc_267_, 20, v_divMod_260_);
lean_ctor_set(v_reuseFailAlloc_267_, 21, v_nonlinearOccs_261_);
lean_ctor_set_uint8(v_reuseFailAlloc_267_, sizeof(void*)*22, v_caseSplits_254_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*22 + 1, v_a_237_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_269_, lean_object* v_s_270_){
_start:
{
uint8_t v_a_125640__boxed_271_; lean_object* v_res_272_; 
v_a_125640__boxed_271_ = lean_unbox(v_a_269_);
v_res_272_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_125640__boxed_271_, v_s_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_env_280_; uint8_t v___x_281_; lean_object* v_env_282_; lean_object* v___x_283_; lean_object* v_toCold_284_; lean_object* v_mctx_285_; lean_object* v_lctx_286_; lean_object* v_options_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v___x_281_ = 0;
v_env_282_ = l_Lean_Environment_setRecordingDeps(v_env_280_, v___x_281_);
v___x_283_ = lean_st_ref_get(v___y_275_);
v_toCold_284_ = lean_ctor_get(v___y_276_, 0);
v_mctx_285_ = lean_ctor_get(v___x_283_, 0);
lean_inc_ref(v_mctx_285_);
lean_dec(v___x_283_);
v_lctx_286_ = lean_ctor_get(v___y_274_, 2);
v_options_287_ = lean_ctor_get(v_toCold_284_, 2);
lean_inc_ref(v_options_287_);
lean_inc_ref(v_lctx_286_);
v___x_288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_288_, 0, v_env_282_);
lean_ctor_set(v___x_288_, 1, v_mctx_285_);
lean_ctor_set(v___x_288_, 2, v_lctx_286_);
lean_ctor_set(v___x_288_, 3, v_options_287_);
v___x_289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_msgData_273_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_ref_304_; lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_ref_304_ = lean_ctor_get(v___y_301_, 2);
v___x_305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_inc(v_ref_304_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_ref_304_);
lean_ctor_set(v___x_310_, 1, v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_324_ = l_Lean_stringToMessageData(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
lean_inc_ref(v_type_325_);
v___x_338_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_325_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_351_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_351_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_351_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_351_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
if (lean_obj_tag(v_a_339_) == 1)
{
lean_object* v_val_343_; lean_object* v___x_345_; 
lean_dec_ref(v_type_325_);
v_val_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_a_339_, 1);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_val_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_val_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
v___x_347_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_348_ = l_Lean_indentExpr(v_type_325_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_349_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
return v___x_350_;
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v_type_325_);
v_a_352_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_338_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_338_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_374_, lean_object* v_u_375_, lean_object* v_instDeclName_376_, lean_object* v_declName_377_, lean_object* v_expectedInst_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_391_ = lean_box(0);
lean_inc_n(v_u_375_, 2);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_u_375_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v_u_375_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v_u_375_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_inc_ref(v___x_394_);
v___x_395_ = l_Lean_mkConst(v_instDeclName_376_, v___x_394_);
lean_inc_ref_n(v_type_374_, 3);
v___x_396_ = l_Lean_mkApp3(v___x_395_, v_type_374_, v_type_374_, v_type_374_);
v___x_397_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_396_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_n(v_a_398_, 2);
lean_dec_ref_known(v___x_397_, 1);
lean_inc(v_declName_377_);
v___x_399_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_377_, v_a_398_, v_expectedInst_378_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_400_ = l_Lean_mkConst(v_declName_377_, v___x_394_);
lean_inc_ref_n(v_type_374_, 2);
v___x_401_ = l_Lean_mkApp4(v___x_400_, v_type_374_, v_type_374_, v_type_374_, v_a_398_);
v___x_402_ = l_Lean_Meta_Sym_canon(v___x_401_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = l_Lean_Meta_Sym_shareCommon(v_a_403_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_404_;
}
else
{
return v___x_402_;
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_398_);
lean_dec_ref_known(v___x_394_, 2);
lean_dec(v_declName_377_);
lean_dec_ref(v_type_374_);
v_a_405_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_399_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_394_, 2);
lean_dec_ref(v_expectedInst_378_);
lean_dec(v_declName_377_);
lean_dec_ref(v_type_374_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_413_ = _args[0];
lean_object* v_u_414_ = _args[1];
lean_object* v_instDeclName_415_ = _args[2];
lean_object* v_declName_416_ = _args[3];
lean_object* v_expectedInst_417_ = _args[4];
lean_object* v___y_418_ = _args[5];
lean_object* v___y_419_ = _args[6];
lean_object* v___y_420_ = _args[7];
lean_object* v___y_421_ = _args[8];
lean_object* v___y_422_ = _args[9];
lean_object* v___y_423_ = _args[10];
lean_object* v___y_424_ = _args[11];
lean_object* v___y_425_ = _args[12];
lean_object* v___y_426_ = _args[13];
lean_object* v___y_427_ = _args[14];
lean_object* v___y_428_ = _args[15];
lean_object* v___y_429_ = _args[16];
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_413_, v_u_414_, v_instDeclName_415_, v_declName_416_, v_expectedInst_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_431_, lean_object* v_s_432_){
_start:
{
lean_object* v_toRing_433_; lean_object* v_invFn_x3f_434_; lean_object* v_divFn_x3f_435_; lean_object* v_zpowFn_x3f_436_; lean_object* v_semiringId_x3f_437_; lean_object* v_commSemiringInst_438_; lean_object* v_commRingInst_439_; lean_object* v_noZeroDivInst_x3f_440_; lean_object* v_fieldInst_x3f_441_; lean_object* v_powIdentityInst_x3f_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_474_; 
v_toRing_433_ = lean_ctor_get(v_s_432_, 0);
v_invFn_x3f_434_ = lean_ctor_get(v_s_432_, 1);
v_divFn_x3f_435_ = lean_ctor_get(v_s_432_, 2);
v_zpowFn_x3f_436_ = lean_ctor_get(v_s_432_, 3);
v_semiringId_x3f_437_ = lean_ctor_get(v_s_432_, 4);
v_commSemiringInst_438_ = lean_ctor_get(v_s_432_, 5);
v_commRingInst_439_ = lean_ctor_get(v_s_432_, 6);
v_noZeroDivInst_x3f_440_ = lean_ctor_get(v_s_432_, 7);
v_fieldInst_x3f_441_ = lean_ctor_get(v_s_432_, 8);
v_powIdentityInst_x3f_442_ = lean_ctor_get(v_s_432_, 9);
v_isSharedCheck_474_ = !lean_is_exclusive(v_s_432_);
if (v_isSharedCheck_474_ == 0)
{
v___x_444_ = v_s_432_;
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_powIdentityInst_x3f_442_);
lean_inc(v_fieldInst_x3f_441_);
lean_inc(v_noZeroDivInst_x3f_440_);
lean_inc(v_commRingInst_439_);
lean_inc(v_commSemiringInst_438_);
lean_inc(v_semiringId_x3f_437_);
lean_inc(v_zpowFn_x3f_436_);
lean_inc(v_divFn_x3f_435_);
lean_inc(v_invFn_x3f_434_);
lean_inc(v_toRing_433_);
lean_dec(v_s_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_id_446_; lean_object* v_type_447_; lean_object* v_u_448_; lean_object* v_ringInst_449_; lean_object* v_semiringInst_450_; lean_object* v_charInst_x3f_451_; uint8_t v_symbolicChar_452_; lean_object* v_mulFn_x3f_453_; lean_object* v_subFn_x3f_454_; lean_object* v_negFn_x3f_455_; lean_object* v_powFn_x3f_456_; lean_object* v_intCastFn_x3f_457_; lean_object* v_natCastFn_x3f_458_; lean_object* v_natSMulFn_x3f_459_; lean_object* v_intSMulFn_x3f_460_; lean_object* v_one_x3f_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_472_; 
v_id_446_ = lean_ctor_get(v_toRing_433_, 0);
v_type_447_ = lean_ctor_get(v_toRing_433_, 1);
v_u_448_ = lean_ctor_get(v_toRing_433_, 2);
v_ringInst_449_ = lean_ctor_get(v_toRing_433_, 3);
v_semiringInst_450_ = lean_ctor_get(v_toRing_433_, 4);
v_charInst_x3f_451_ = lean_ctor_get(v_toRing_433_, 5);
v_symbolicChar_452_ = lean_ctor_get_uint8(v_toRing_433_, sizeof(void*)*16);
v_mulFn_x3f_453_ = lean_ctor_get(v_toRing_433_, 7);
v_subFn_x3f_454_ = lean_ctor_get(v_toRing_433_, 8);
v_negFn_x3f_455_ = lean_ctor_get(v_toRing_433_, 9);
v_powFn_x3f_456_ = lean_ctor_get(v_toRing_433_, 10);
v_intCastFn_x3f_457_ = lean_ctor_get(v_toRing_433_, 11);
v_natCastFn_x3f_458_ = lean_ctor_get(v_toRing_433_, 12);
v_natSMulFn_x3f_459_ = lean_ctor_get(v_toRing_433_, 13);
v_intSMulFn_x3f_460_ = lean_ctor_get(v_toRing_433_, 14);
v_one_x3f_461_ = lean_ctor_get(v_toRing_433_, 15);
v_isSharedCheck_472_ = !lean_is_exclusive(v_toRing_433_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_toRing_433_, 6);
lean_dec(v_unused_473_);
v___x_463_ = v_toRing_433_;
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_one_x3f_461_);
lean_inc(v_intSMulFn_x3f_460_);
lean_inc(v_natSMulFn_x3f_459_);
lean_inc(v_natCastFn_x3f_458_);
lean_inc(v_intCastFn_x3f_457_);
lean_inc(v_powFn_x3f_456_);
lean_inc(v_negFn_x3f_455_);
lean_inc(v_subFn_x3f_454_);
lean_inc(v_mulFn_x3f_453_);
lean_inc(v_charInst_x3f_451_);
lean_inc(v_semiringInst_450_);
lean_inc(v_ringInst_449_);
lean_inc(v_u_448_);
lean_inc(v_type_447_);
lean_inc(v_id_446_);
lean_dec(v_toRing_433_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_a_431_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 6, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_id_446_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_type_447_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_u_448_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_ringInst_449_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_semiringInst_450_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_charInst_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_mulFn_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_subFn_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_471_, 9, v_negFn_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 10, v_powFn_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 11, v_intCastFn_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 12, v_natCastFn_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 13, v_natSMulFn_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 14, v_intSMulFn_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 15, v_one_x3f_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*16, v_symbolicChar_452_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_467_);
v___x_469_ = v___x_444_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_invFn_x3f_434_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_divFn_x3f_435_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_zpowFn_x3f_436_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_semiringId_x3f_437_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_commSemiringInst_438_);
lean_ctor_set(v_reuseFailAlloc_470_, 6, v_commRingInst_439_);
lean_ctor_set(v_reuseFailAlloc_470_, 7, v_noZeroDivInst_x3f_440_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_fieldInst_x3f_441_);
lean_ctor_set(v_reuseFailAlloc_470_, 9, v_powIdentityInst_x3f_442_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_550_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_550_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_550_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_550_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_toRing_511_; lean_object* v_addFn_x3f_512_; 
v_toRing_511_ = lean_ctor_get(v_a_507_, 0);
lean_inc_ref(v_toRing_511_);
lean_dec(v_a_507_);
v_addFn_x3f_512_ = lean_ctor_get(v_toRing_511_, 6);
if (lean_obj_tag(v_addFn_x3f_512_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_515_; 
lean_inc_ref(v_addFn_x3f_512_);
lean_dec_ref(v_toRing_511_);
v_val_513_ = lean_ctor_get(v_addFn_x3f_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_addFn_x3f_512_, 1);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_val_513_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_val_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v_type_517_; lean_object* v_u_518_; lean_object* v_semiringInst_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_expectedInst_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_del_object(v___x_509_);
v_type_517_ = lean_ctor_get(v_toRing_511_, 1);
lean_inc_ref_n(v_type_517_, 3);
v_u_518_ = lean_ctor_get(v_toRing_511_, 2);
lean_inc_n(v_u_518_, 2);
v_semiringInst_519_ = lean_ctor_get(v_toRing_511_, 4);
lean_inc_ref(v_semiringInst_519_);
lean_dec_ref(v_toRing_511_);
v___x_520_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v_u_518_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_inc_ref(v___x_522_);
v___x_523_ = l_Lean_mkConst(v___x_520_, v___x_522_);
v___x_524_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6));
v___x_525_ = l_Lean_mkConst(v___x_524_, v___x_522_);
v___x_526_ = l_Lean_mkAppB(v___x_525_, v_type_517_, v_semiringInst_519_);
v_expectedInst_527_ = l_Lean_mkAppB(v___x_523_, v_type_517_, v___x_526_);
v___x_528_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8));
v___x_529_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10));
v___x_530_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_517_, v_u_518_, v___x_528_, v___x_529_, v_expectedInst_527_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_n(v_a_531_, 2);
lean_dec_ref_known(v___x_530_, 1);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_532_, 0, v_a_531_);
v___x_533_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_532_, v___y_494_, v___y_500_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v___x_533_, 0);
lean_dec(v_unused_541_);
v___x_535_ = v___x_533_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_dec(v___x_533_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_a_531_);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_531_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_a_531_);
v_a_542_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_533_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_533_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_506_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_506_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_572_, lean_object* v_u_573_, lean_object* v_instDeclName_574_, lean_object* v_declName_575_, lean_object* v_expectedInst_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v_u_573_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
lean_inc_ref(v___x_590_);
v___x_591_ = l_Lean_mkConst(v_instDeclName_574_, v___x_590_);
lean_inc_ref(v_type_572_);
v___x_592_ = l_Lean_Expr_app___override(v___x_591_, v_type_572_);
v___x_593_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_592_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_n(v_a_594_, 2);
lean_dec_ref_known(v___x_593_, 1);
lean_inc(v_declName_575_);
v___x_595_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_575_, v_a_594_, v_expectedInst_576_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref_known(v___x_595_, 1);
v___x_596_ = l_Lean_mkConst(v_declName_575_, v___x_590_);
v___x_597_ = l_Lean_mkAppB(v___x_596_, v_type_572_, v_a_594_);
v___x_598_ = l_Lean_Meta_Sym_canon(v___x_597_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = l_Lean_Meta_Sym_shareCommon(v_a_599_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_600_;
}
else
{
return v___x_598_;
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_594_);
lean_dec_ref_known(v___x_590_, 2);
lean_dec(v_declName_575_);
lean_dec_ref(v_type_572_);
v_a_601_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_595_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_595_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_590_, 2);
lean_dec_ref(v_expectedInst_576_);
lean_dec(v_declName_575_);
lean_dec_ref(v_type_572_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_609_ = _args[0];
lean_object* v_u_610_ = _args[1];
lean_object* v_instDeclName_611_ = _args[2];
lean_object* v_declName_612_ = _args[3];
lean_object* v_expectedInst_613_ = _args[4];
lean_object* v___y_614_ = _args[5];
lean_object* v___y_615_ = _args[6];
lean_object* v___y_616_ = _args[7];
lean_object* v___y_617_ = _args[8];
lean_object* v___y_618_ = _args[9];
lean_object* v___y_619_ = _args[10];
lean_object* v___y_620_ = _args[11];
lean_object* v___y_621_ = _args[12];
lean_object* v___y_622_ = _args[13];
lean_object* v___y_623_ = _args[14];
lean_object* v___y_624_ = _args[15];
lean_object* v___y_625_ = _args[16];
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_609_, v_u_610_, v_instDeclName_611_, v_declName_612_, v_expectedInst_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_627_, lean_object* v_s_628_){
_start:
{
lean_object* v_toRing_629_; lean_object* v_invFn_x3f_630_; lean_object* v_divFn_x3f_631_; lean_object* v_zpowFn_x3f_632_; lean_object* v_semiringId_x3f_633_; lean_object* v_commSemiringInst_634_; lean_object* v_commRingInst_635_; lean_object* v_noZeroDivInst_x3f_636_; lean_object* v_fieldInst_x3f_637_; lean_object* v_powIdentityInst_x3f_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_670_; 
v_toRing_629_ = lean_ctor_get(v_s_628_, 0);
v_invFn_x3f_630_ = lean_ctor_get(v_s_628_, 1);
v_divFn_x3f_631_ = lean_ctor_get(v_s_628_, 2);
v_zpowFn_x3f_632_ = lean_ctor_get(v_s_628_, 3);
v_semiringId_x3f_633_ = lean_ctor_get(v_s_628_, 4);
v_commSemiringInst_634_ = lean_ctor_get(v_s_628_, 5);
v_commRingInst_635_ = lean_ctor_get(v_s_628_, 6);
v_noZeroDivInst_x3f_636_ = lean_ctor_get(v_s_628_, 7);
v_fieldInst_x3f_637_ = lean_ctor_get(v_s_628_, 8);
v_powIdentityInst_x3f_638_ = lean_ctor_get(v_s_628_, 9);
v_isSharedCheck_670_ = !lean_is_exclusive(v_s_628_);
if (v_isSharedCheck_670_ == 0)
{
v___x_640_ = v_s_628_;
v_isShared_641_ = v_isSharedCheck_670_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_powIdentityInst_x3f_638_);
lean_inc(v_fieldInst_x3f_637_);
lean_inc(v_noZeroDivInst_x3f_636_);
lean_inc(v_commRingInst_635_);
lean_inc(v_commSemiringInst_634_);
lean_inc(v_semiringId_x3f_633_);
lean_inc(v_zpowFn_x3f_632_);
lean_inc(v_divFn_x3f_631_);
lean_inc(v_invFn_x3f_630_);
lean_inc(v_toRing_629_);
lean_dec(v_s_628_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_670_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_id_642_; lean_object* v_type_643_; lean_object* v_u_644_; lean_object* v_ringInst_645_; lean_object* v_semiringInst_646_; lean_object* v_charInst_x3f_647_; uint8_t v_symbolicChar_648_; lean_object* v_addFn_x3f_649_; lean_object* v_mulFn_x3f_650_; lean_object* v_subFn_x3f_651_; lean_object* v_powFn_x3f_652_; lean_object* v_intCastFn_x3f_653_; lean_object* v_natCastFn_x3f_654_; lean_object* v_natSMulFn_x3f_655_; lean_object* v_intSMulFn_x3f_656_; lean_object* v_one_x3f_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_668_; 
v_id_642_ = lean_ctor_get(v_toRing_629_, 0);
v_type_643_ = lean_ctor_get(v_toRing_629_, 1);
v_u_644_ = lean_ctor_get(v_toRing_629_, 2);
v_ringInst_645_ = lean_ctor_get(v_toRing_629_, 3);
v_semiringInst_646_ = lean_ctor_get(v_toRing_629_, 4);
v_charInst_x3f_647_ = lean_ctor_get(v_toRing_629_, 5);
v_symbolicChar_648_ = lean_ctor_get_uint8(v_toRing_629_, sizeof(void*)*16);
v_addFn_x3f_649_ = lean_ctor_get(v_toRing_629_, 6);
v_mulFn_x3f_650_ = lean_ctor_get(v_toRing_629_, 7);
v_subFn_x3f_651_ = lean_ctor_get(v_toRing_629_, 8);
v_powFn_x3f_652_ = lean_ctor_get(v_toRing_629_, 10);
v_intCastFn_x3f_653_ = lean_ctor_get(v_toRing_629_, 11);
v_natCastFn_x3f_654_ = lean_ctor_get(v_toRing_629_, 12);
v_natSMulFn_x3f_655_ = lean_ctor_get(v_toRing_629_, 13);
v_intSMulFn_x3f_656_ = lean_ctor_get(v_toRing_629_, 14);
v_one_x3f_657_ = lean_ctor_get(v_toRing_629_, 15);
v_isSharedCheck_668_ = !lean_is_exclusive(v_toRing_629_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_toRing_629_, 9);
lean_dec(v_unused_669_);
v___x_659_ = v_toRing_629_;
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_one_x3f_657_);
lean_inc(v_intSMulFn_x3f_656_);
lean_inc(v_natSMulFn_x3f_655_);
lean_inc(v_natCastFn_x3f_654_);
lean_inc(v_intCastFn_x3f_653_);
lean_inc(v_powFn_x3f_652_);
lean_inc(v_subFn_x3f_651_);
lean_inc(v_mulFn_x3f_650_);
lean_inc(v_addFn_x3f_649_);
lean_inc(v_charInst_x3f_647_);
lean_inc(v_semiringInst_646_);
lean_inc(v_ringInst_645_);
lean_inc(v_u_644_);
lean_inc(v_type_643_);
lean_inc(v_id_642_);
lean_dec(v_toRing_629_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_a_627_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 9, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_id_642_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_type_643_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_u_644_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_ringInst_645_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_semiringInst_646_);
lean_ctor_set(v_reuseFailAlloc_667_, 5, v_charInst_x3f_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 6, v_addFn_x3f_649_);
lean_ctor_set(v_reuseFailAlloc_667_, 7, v_mulFn_x3f_650_);
lean_ctor_set(v_reuseFailAlloc_667_, 8, v_subFn_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 9, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_667_, 10, v_powFn_x3f_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 11, v_intCastFn_x3f_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 12, v_natCastFn_x3f_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 13, v_natSMulFn_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 14, v_intSMulFn_x3f_656_);
lean_ctor_set(v_reuseFailAlloc_667_, 15, v_one_x3f_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_667_, sizeof(void*)*16, v_symbolicChar_648_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_663_);
v___x_665_ = v___x_640_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_invFn_x3f_630_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_divFn_x3f_631_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_zpowFn_x3f_632_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v_semiringId_x3f_633_);
lean_ctor_set(v_reuseFailAlloc_666_, 5, v_commSemiringInst_634_);
lean_ctor_set(v_reuseFailAlloc_666_, 6, v_commRingInst_635_);
lean_ctor_set(v_reuseFailAlloc_666_, 7, v_noZeroDivInst_x3f_636_);
lean_ctor_set(v_reuseFailAlloc_666_, 8, v_fieldInst_x3f_637_);
lean_ctor_set(v_reuseFailAlloc_666_, 9, v_powIdentityInst_x3f_638_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_738_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_738_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_738_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_738_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_toRing_702_; lean_object* v_negFn_x3f_703_; 
v_toRing_702_ = lean_ctor_get(v_a_698_, 0);
lean_inc_ref(v_toRing_702_);
lean_dec(v_a_698_);
v_negFn_x3f_703_ = lean_ctor_get(v_toRing_702_, 9);
if (lean_obj_tag(v_negFn_x3f_703_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_706_; 
lean_inc_ref(v_negFn_x3f_703_);
lean_dec_ref(v_toRing_702_);
v_val_704_ = lean_ctor_get(v_negFn_x3f_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_negFn_x3f_703_, 1);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_val_704_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_val_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v_type_708_; lean_object* v_u_709_; lean_object* v_ringInst_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_expectedInst_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_700_);
v_type_708_ = lean_ctor_get(v_toRing_702_, 1);
lean_inc_ref_n(v_type_708_, 2);
v_u_709_ = lean_ctor_get(v_toRing_702_, 2);
lean_inc_n(v_u_709_, 2);
v_ringInst_710_ = lean_ctor_get(v_toRing_702_, 3);
lean_inc_ref(v_ringInst_710_);
lean_dec_ref(v_toRing_702_);
v___x_711_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2));
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_713_, 0, v_u_709_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_mkConst(v___x_711_, v___x_713_);
v_expectedInst_715_ = l_Lean_mkAppB(v___x_714_, v_type_708_, v_ringInst_710_);
v___x_716_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_717_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_718_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_708_, v_u_709_, v___x_716_, v___x_717_, v_expectedInst_715_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___f_720_; lean_object* v___x_721_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_n(v_a_719_, 2);
lean_dec_ref_known(v___x_718_, 1);
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_720_, 0, v_a_719_);
v___x_721_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_720_, v___y_685_, v___y_691_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_729_);
v___x_723_ = v___x_721_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_721_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_a_719_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_719_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_719_);
v_a_730_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_697_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_697_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_nat_to_int(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_848_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_848_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_848_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_848_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_toRing_792_; lean_object* v_type_793_; lean_object* v_u_794_; lean_object* v_semiringInst_795_; lean_object* v___x_796_; lean_object* v_n_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_ofNatInst_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_toRing_792_ = lean_ctor_get(v_a_788_, 0);
lean_inc_ref(v_toRing_792_);
lean_dec(v_a_788_);
v_type_793_ = lean_ctor_get(v_toRing_792_, 1);
lean_inc_ref_n(v_type_793_, 2);
v_u_794_ = lean_ctor_get(v_toRing_792_, 2);
lean_inc(v_u_794_);
v_semiringInst_795_ = lean_ctor_get(v_toRing_792_, 4);
lean_inc_ref(v_semiringInst_795_);
lean_dec_ref(v_toRing_792_);
v___x_796_ = lean_nat_abs(v_k_774_);
v_n_797_ = l_Lean_mkRawNatLit(v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_800_, 0, v_u_794_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_inc_ref(v___x_800_);
v___x_832_ = l_Lean_mkConst(v___x_798_, v___x_800_);
lean_inc_ref(v_n_797_);
v___x_833_ = l_Lean_mkAppB(v___x_832_, v_type_793_, v_n_797_);
v___x_834_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_833_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
if (lean_obj_tag(v_a_835_) == 1)
{
lean_object* v_val_836_; 
lean_dec_ref(v_semiringInst_795_);
v_val_836_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_a_835_, 1);
v_ofNatInst_802_ = v_val_836_;
v___y_803_ = v___y_775_;
v___y_804_ = v___y_776_;
v___y_805_ = v___y_777_;
v___y_806_ = v___y_778_;
v___y_807_ = v___y_779_;
v___y_808_ = v___y_780_;
v___y_809_ = v___y_781_;
v___y_810_ = v___y_782_;
v___y_811_ = v___y_783_;
v___y_812_ = v___y_784_;
v___y_813_ = v___y_785_;
goto v___jp_801_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_a_835_);
v___x_837_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5));
lean_inc_ref(v___x_800_);
v___x_838_ = l_Lean_mkConst(v___x_837_, v___x_800_);
lean_inc_ref(v_n_797_);
lean_inc_ref(v_type_793_);
v___x_839_ = l_Lean_mkApp3(v___x_838_, v_type_793_, v_semiringInst_795_, v_n_797_);
v_ofNatInst_802_ = v___x_839_;
v___y_803_ = v___y_775_;
v___y_804_ = v___y_776_;
v___y_805_ = v___y_777_;
v___y_806_ = v___y_778_;
v___y_807_ = v___y_779_;
v___y_808_ = v___y_780_;
v___y_809_ = v___y_781_;
v___y_810_ = v___y_782_;
v___y_811_ = v___y_783_;
v___y_812_ = v___y_784_;
v___y_813_ = v___y_785_;
goto v___jp_801_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref_known(v___x_800_, 2);
lean_dec_ref(v_n_797_);
lean_dec_ref(v_semiringInst_795_);
lean_dec_ref(v_type_793_);
lean_del_object(v___x_790_);
v_a_840_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_834_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_834_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
v___jp_801_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_e_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_814_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_815_ = l_Lean_mkConst(v___x_814_, v___x_800_);
v_e_816_ = l_Lean_mkApp3(v___x_815_, v_type_793_, v_n_797_, v_ofNatInst_802_);
v___x_817_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_818_ = lean_int_dec_lt(v_k_774_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_e_816_);
v___x_820_ = v___x_790_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_e_816_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_822_; 
lean_del_object(v___x_790_);
v___x_822_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = l_Lean_Expr_app___override(v_a_823_, v_e_816_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_dec_ref(v_e_816_);
return v___x_822_;
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_787_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_787_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v_k_857_);
return v_res_870_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = l_Lean_Level_ofNat(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_881_, lean_object* v_type_882_, lean_object* v_semiringInst_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_898_ = lean_box(0);
lean_inc(v_u_881_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v_u_881_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
lean_inc_ref(v___x_899_);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v_u_881_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
lean_inc_ref(v___x_901_);
v___x_902_ = l_Lean_mkConst(v___x_896_, v___x_901_);
v___x_903_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_882_, 2);
v___x_904_ = l_Lean_mkApp3(v___x_902_, v_type_882_, v___x_903_, v_type_882_);
v___x_905_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_904_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_inst_x27_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_n(v_a_906_, 2);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_908_ = l_Lean_mkConst(v___x_907_, v___x_899_);
lean_inc_ref(v_type_882_);
v_inst_x27_909_ = l_Lean_mkAppB(v___x_908_, v_type_882_, v_semiringInst_883_);
v___x_910_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_911_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_910_, v_a_906_, v_inst_x27_909_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v___x_911_, 1);
v___x_912_ = l_Lean_mkConst(v___x_910_, v___x_901_);
lean_inc_ref(v_type_882_);
v___x_913_ = l_Lean_mkApp4(v___x_912_, v_type_882_, v___x_903_, v_type_882_, v_a_906_);
v___x_914_ = l_Lean_Meta_Sym_canon(v___x_913_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Meta_Sym_shareCommon(v_a_915_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_916_;
}
else
{
return v___x_914_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_906_);
lean_dec_ref_known(v___x_901_, 2);
lean_dec_ref(v_type_882_);
v_a_917_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_911_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_911_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_901_, 2);
lean_dec_ref_known(v___x_899_, 2);
lean_dec_ref(v_semiringInst_883_);
lean_dec_ref(v_type_882_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_925_, lean_object* v_type_926_, lean_object* v_semiringInst_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_925_, v_type_926_, v_semiringInst_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_941_, lean_object* v_s_942_){
_start:
{
lean_object* v_toRing_943_; lean_object* v_invFn_x3f_944_; lean_object* v_divFn_x3f_945_; lean_object* v_zpowFn_x3f_946_; lean_object* v_semiringId_x3f_947_; lean_object* v_commSemiringInst_948_; lean_object* v_commRingInst_949_; lean_object* v_noZeroDivInst_x3f_950_; lean_object* v_fieldInst_x3f_951_; lean_object* v_powIdentityInst_x3f_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_984_; 
v_toRing_943_ = lean_ctor_get(v_s_942_, 0);
v_invFn_x3f_944_ = lean_ctor_get(v_s_942_, 1);
v_divFn_x3f_945_ = lean_ctor_get(v_s_942_, 2);
v_zpowFn_x3f_946_ = lean_ctor_get(v_s_942_, 3);
v_semiringId_x3f_947_ = lean_ctor_get(v_s_942_, 4);
v_commSemiringInst_948_ = lean_ctor_get(v_s_942_, 5);
v_commRingInst_949_ = lean_ctor_get(v_s_942_, 6);
v_noZeroDivInst_x3f_950_ = lean_ctor_get(v_s_942_, 7);
v_fieldInst_x3f_951_ = lean_ctor_get(v_s_942_, 8);
v_powIdentityInst_x3f_952_ = lean_ctor_get(v_s_942_, 9);
v_isSharedCheck_984_ = !lean_is_exclusive(v_s_942_);
if (v_isSharedCheck_984_ == 0)
{
v___x_954_ = v_s_942_;
v_isShared_955_ = v_isSharedCheck_984_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_powIdentityInst_x3f_952_);
lean_inc(v_fieldInst_x3f_951_);
lean_inc(v_noZeroDivInst_x3f_950_);
lean_inc(v_commRingInst_949_);
lean_inc(v_commSemiringInst_948_);
lean_inc(v_semiringId_x3f_947_);
lean_inc(v_zpowFn_x3f_946_);
lean_inc(v_divFn_x3f_945_);
lean_inc(v_invFn_x3f_944_);
lean_inc(v_toRing_943_);
lean_dec(v_s_942_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_984_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_id_956_; lean_object* v_type_957_; lean_object* v_u_958_; lean_object* v_ringInst_959_; lean_object* v_semiringInst_960_; lean_object* v_charInst_x3f_961_; uint8_t v_symbolicChar_962_; lean_object* v_addFn_x3f_963_; lean_object* v_mulFn_x3f_964_; lean_object* v_subFn_x3f_965_; lean_object* v_negFn_x3f_966_; lean_object* v_intCastFn_x3f_967_; lean_object* v_natCastFn_x3f_968_; lean_object* v_natSMulFn_x3f_969_; lean_object* v_intSMulFn_x3f_970_; lean_object* v_one_x3f_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_982_; 
v_id_956_ = lean_ctor_get(v_toRing_943_, 0);
v_type_957_ = lean_ctor_get(v_toRing_943_, 1);
v_u_958_ = lean_ctor_get(v_toRing_943_, 2);
v_ringInst_959_ = lean_ctor_get(v_toRing_943_, 3);
v_semiringInst_960_ = lean_ctor_get(v_toRing_943_, 4);
v_charInst_x3f_961_ = lean_ctor_get(v_toRing_943_, 5);
v_symbolicChar_962_ = lean_ctor_get_uint8(v_toRing_943_, sizeof(void*)*16);
v_addFn_x3f_963_ = lean_ctor_get(v_toRing_943_, 6);
v_mulFn_x3f_964_ = lean_ctor_get(v_toRing_943_, 7);
v_subFn_x3f_965_ = lean_ctor_get(v_toRing_943_, 8);
v_negFn_x3f_966_ = lean_ctor_get(v_toRing_943_, 9);
v_intCastFn_x3f_967_ = lean_ctor_get(v_toRing_943_, 11);
v_natCastFn_x3f_968_ = lean_ctor_get(v_toRing_943_, 12);
v_natSMulFn_x3f_969_ = lean_ctor_get(v_toRing_943_, 13);
v_intSMulFn_x3f_970_ = lean_ctor_get(v_toRing_943_, 14);
v_one_x3f_971_ = lean_ctor_get(v_toRing_943_, 15);
v_isSharedCheck_982_ = !lean_is_exclusive(v_toRing_943_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_toRing_943_, 10);
lean_dec(v_unused_983_);
v___x_973_ = v_toRing_943_;
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_one_x3f_971_);
lean_inc(v_intSMulFn_x3f_970_);
lean_inc(v_natSMulFn_x3f_969_);
lean_inc(v_natCastFn_x3f_968_);
lean_inc(v_intCastFn_x3f_967_);
lean_inc(v_negFn_x3f_966_);
lean_inc(v_subFn_x3f_965_);
lean_inc(v_mulFn_x3f_964_);
lean_inc(v_addFn_x3f_963_);
lean_inc(v_charInst_x3f_961_);
lean_inc(v_semiringInst_960_);
lean_inc(v_ringInst_959_);
lean_inc(v_u_958_);
lean_inc(v_type_957_);
lean_inc(v_id_956_);
lean_dec(v_toRing_943_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_a_941_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 10, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_id_956_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_type_957_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_u_958_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_ringInst_959_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_semiringInst_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_charInst_x3f_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_addFn_x3f_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_mulFn_x3f_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_subFn_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 9, v_negFn_x3f_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 10, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_981_, 11, v_intCastFn_x3f_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 12, v_natCastFn_x3f_968_);
lean_ctor_set(v_reuseFailAlloc_981_, 13, v_natSMulFn_x3f_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 14, v_intSMulFn_x3f_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 15, v_one_x3f_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*16, v_symbolicChar_962_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_977_);
v___x_979_ = v___x_954_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_invFn_x3f_944_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_divFn_x3f_945_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_zpowFn_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_semiringId_x3f_947_);
lean_ctor_set(v_reuseFailAlloc_980_, 5, v_commSemiringInst_948_);
lean_ctor_set(v_reuseFailAlloc_980_, 6, v_commRingInst_949_);
lean_ctor_set(v_reuseFailAlloc_980_, 7, v_noZeroDivInst_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_980_, 8, v_fieldInst_x3f_951_);
lean_ctor_set(v_reuseFailAlloc_980_, 9, v_powIdentityInst_x3f_952_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1031_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1031_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1031_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_toRing_1002_; lean_object* v_powFn_x3f_1003_; 
v_toRing_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc_ref(v_toRing_1002_);
lean_dec(v_a_998_);
v_powFn_x3f_1003_ = lean_ctor_get(v_toRing_1002_, 10);
if (lean_obj_tag(v_powFn_x3f_1003_) == 1)
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
lean_inc_ref(v_powFn_x3f_1003_);
lean_dec_ref(v_toRing_1002_);
v_val_1004_ = lean_ctor_get(v_powFn_x3f_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_powFn_x3f_1003_, 1);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_type_1008_; lean_object* v_u_1009_; lean_object* v_semiringInst_1010_; lean_object* v___x_1011_; 
lean_del_object(v___x_1000_);
v_type_1008_ = lean_ctor_get(v_toRing_1002_, 1);
lean_inc_ref(v_type_1008_);
v_u_1009_ = lean_ctor_get(v_toRing_1002_, 2);
lean_inc(v_u_1009_);
v_semiringInst_1010_ = lean_ctor_get(v_toRing_1002_, 4);
lean_inc_ref(v_semiringInst_1010_);
lean_dec_ref(v_toRing_1002_);
v___x_1011_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1009_, v_type_1008_, v_semiringInst_1010_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_n(v_a_1012_, 2);
lean_dec_ref_known(v___x_1011_, 1);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1013_, 0, v_a_1012_);
v___x_1014_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1013_, v___y_985_, v___y_991_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1022_);
v___x_1016_ = v___x_1014_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1014_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v_a_1012_);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1012_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1012_);
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1014_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1014_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_997_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_997_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_x_1066_; lean_object* v_k_1067_; lean_object* v___y_1069_; lean_object* v_a_1070_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_x_1066_ = lean_ctor_get(v_pw_1053_, 0);
lean_inc(v_x_1066_);
v_k_1067_ = lean_ctor_get(v_pw_1053_, 1);
lean_inc(v_k_1067_);
lean_dec_ref(v_pw_1053_);
v___x_1084_ = l_Lean_instInhabitedExpr;
v___x_1085_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_1054_, v___y_1055_, v___y_1063_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1102_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_toRingState_1090_; lean_object* v_vars_1091_; lean_object* v_size_1092_; uint8_t v___x_1093_; 
v_toRingState_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc_ref(v_toRingState_1090_);
lean_dec(v_a_1086_);
v_vars_1091_ = lean_ctor_get(v_toRingState_1090_, 0);
lean_inc_ref(v_vars_1091_);
lean_dec_ref(v_toRingState_1090_);
v_size_1092_ = lean_ctor_get(v_vars_1091_, 2);
v___x_1093_ = lean_nat_dec_lt(v_x_1066_, v_size_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_dec_ref(v_vars_1091_);
lean_dec(v_x_1066_);
v___x_1094_ = l_outOfBounds___redArg(v___x_1084_);
lean_inc(v___x_1094_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1094_);
v___x_1096_ = v___x_1088_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v___y_1069_ = v___x_1096_;
v_a_1070_ = v___x_1094_;
goto v___jp_1068_;
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1084_, v_vars_1091_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec_ref(v_vars_1091_);
lean_inc(v___x_1098_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1098_);
v___x_1100_ = v___x_1088_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v___y_1069_ = v___x_1100_;
v_a_1070_ = v___x_1098_;
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_k_1067_);
lean_dec(v_x_1066_);
v_a_1103_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1085_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1085_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
v___jp_1068_:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_dec_eq(v_k_1067_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec_ref(v___y_1069_);
v___x_1073_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1083_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1078_ = l_Lean_mkNatLit(v_k_1067_);
v___x_1079_ = l_Lean_mkAppB(v_a_1074_, v_a_1070_, v___x_1078_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_dec_ref(v_a_1070_);
lean_dec(v_k_1067_);
return v___x_1073_;
}
}
else
{
lean_dec_ref(v_a_1070_);
lean_dec(v_k_1067_);
return v___y_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_1125_, lean_object* v_s_1126_){
_start:
{
lean_object* v_toRing_1127_; lean_object* v_invFn_x3f_1128_; lean_object* v_divFn_x3f_1129_; lean_object* v_zpowFn_x3f_1130_; lean_object* v_semiringId_x3f_1131_; lean_object* v_commSemiringInst_1132_; lean_object* v_commRingInst_1133_; lean_object* v_noZeroDivInst_x3f_1134_; lean_object* v_fieldInst_x3f_1135_; lean_object* v_powIdentityInst_x3f_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1168_; 
v_toRing_1127_ = lean_ctor_get(v_s_1126_, 0);
v_invFn_x3f_1128_ = lean_ctor_get(v_s_1126_, 1);
v_divFn_x3f_1129_ = lean_ctor_get(v_s_1126_, 2);
v_zpowFn_x3f_1130_ = lean_ctor_get(v_s_1126_, 3);
v_semiringId_x3f_1131_ = lean_ctor_get(v_s_1126_, 4);
v_commSemiringInst_1132_ = lean_ctor_get(v_s_1126_, 5);
v_commRingInst_1133_ = lean_ctor_get(v_s_1126_, 6);
v_noZeroDivInst_x3f_1134_ = lean_ctor_get(v_s_1126_, 7);
v_fieldInst_x3f_1135_ = lean_ctor_get(v_s_1126_, 8);
v_powIdentityInst_x3f_1136_ = lean_ctor_get(v_s_1126_, 9);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_s_1126_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1138_ = v_s_1126_;
v_isShared_1139_ = v_isSharedCheck_1168_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1136_);
lean_inc(v_fieldInst_x3f_1135_);
lean_inc(v_noZeroDivInst_x3f_1134_);
lean_inc(v_commRingInst_1133_);
lean_inc(v_commSemiringInst_1132_);
lean_inc(v_semiringId_x3f_1131_);
lean_inc(v_zpowFn_x3f_1130_);
lean_inc(v_divFn_x3f_1129_);
lean_inc(v_invFn_x3f_1128_);
lean_inc(v_toRing_1127_);
lean_dec(v_s_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1168_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_id_1140_; lean_object* v_type_1141_; lean_object* v_u_1142_; lean_object* v_ringInst_1143_; lean_object* v_semiringInst_1144_; lean_object* v_charInst_x3f_1145_; uint8_t v_symbolicChar_1146_; lean_object* v_addFn_x3f_1147_; lean_object* v_subFn_x3f_1148_; lean_object* v_negFn_x3f_1149_; lean_object* v_powFn_x3f_1150_; lean_object* v_intCastFn_x3f_1151_; lean_object* v_natCastFn_x3f_1152_; lean_object* v_natSMulFn_x3f_1153_; lean_object* v_intSMulFn_x3f_1154_; lean_object* v_one_x3f_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1166_; 
v_id_1140_ = lean_ctor_get(v_toRing_1127_, 0);
v_type_1141_ = lean_ctor_get(v_toRing_1127_, 1);
v_u_1142_ = lean_ctor_get(v_toRing_1127_, 2);
v_ringInst_1143_ = lean_ctor_get(v_toRing_1127_, 3);
v_semiringInst_1144_ = lean_ctor_get(v_toRing_1127_, 4);
v_charInst_x3f_1145_ = lean_ctor_get(v_toRing_1127_, 5);
v_symbolicChar_1146_ = lean_ctor_get_uint8(v_toRing_1127_, sizeof(void*)*16);
v_addFn_x3f_1147_ = lean_ctor_get(v_toRing_1127_, 6);
v_subFn_x3f_1148_ = lean_ctor_get(v_toRing_1127_, 8);
v_negFn_x3f_1149_ = lean_ctor_get(v_toRing_1127_, 9);
v_powFn_x3f_1150_ = lean_ctor_get(v_toRing_1127_, 10);
v_intCastFn_x3f_1151_ = lean_ctor_get(v_toRing_1127_, 11);
v_natCastFn_x3f_1152_ = lean_ctor_get(v_toRing_1127_, 12);
v_natSMulFn_x3f_1153_ = lean_ctor_get(v_toRing_1127_, 13);
v_intSMulFn_x3f_1154_ = lean_ctor_get(v_toRing_1127_, 14);
v_one_x3f_1155_ = lean_ctor_get(v_toRing_1127_, 15);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_toRing_1127_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_toRing_1127_, 7);
lean_dec(v_unused_1167_);
v___x_1157_ = v_toRing_1127_;
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_one_x3f_1155_);
lean_inc(v_intSMulFn_x3f_1154_);
lean_inc(v_natSMulFn_x3f_1153_);
lean_inc(v_natCastFn_x3f_1152_);
lean_inc(v_intCastFn_x3f_1151_);
lean_inc(v_powFn_x3f_1150_);
lean_inc(v_negFn_x3f_1149_);
lean_inc(v_subFn_x3f_1148_);
lean_inc(v_addFn_x3f_1147_);
lean_inc(v_charInst_x3f_1145_);
lean_inc(v_semiringInst_1144_);
lean_inc(v_ringInst_1143_);
lean_inc(v_u_1142_);
lean_inc(v_type_1141_);
lean_inc(v_id_1140_);
lean_dec(v_toRing_1127_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1125_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 7, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_id_1140_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_type_1141_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_u_1142_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_ringInst_1143_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_semiringInst_1144_);
lean_ctor_set(v_reuseFailAlloc_1165_, 5, v_charInst_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1165_, 6, v_addFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1165_, 7, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 8, v_subFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1165_, 9, v_negFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1165_, 10, v_powFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1165_, 11, v_intCastFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1165_, 12, v_natCastFn_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1165_, 13, v_natSMulFn_x3f_1153_);
lean_ctor_set(v_reuseFailAlloc_1165_, 14, v_intSMulFn_x3f_1154_);
lean_ctor_set(v_reuseFailAlloc_1165_, 15, v_one_x3f_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1165_, sizeof(void*)*16, v_symbolicChar_1146_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1161_);
v___x_1163_ = v___x_1138_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_invFn_x3f_1128_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_divFn_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_zpowFn_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_semiringId_x3f_1131_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_commSemiringInst_1132_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_commRingInst_1133_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v_noZeroDivInst_x3f_1134_);
lean_ctor_set(v_reuseFailAlloc_1164_, 8, v_fieldInst_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1164_, 9, v_powIdentityInst_x3f_1136_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1236_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1236_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1236_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_toRing_1197_; lean_object* v_mulFn_x3f_1198_; 
v_toRing_1197_ = lean_ctor_get(v_a_1193_, 0);
lean_inc_ref(v_toRing_1197_);
lean_dec(v_a_1193_);
v_mulFn_x3f_1198_ = lean_ctor_get(v_toRing_1197_, 7);
if (lean_obj_tag(v_mulFn_x3f_1198_) == 1)
{
lean_object* v_val_1199_; lean_object* v___x_1201_; 
lean_inc_ref(v_mulFn_x3f_1198_);
lean_dec_ref(v_toRing_1197_);
v_val_1199_ = lean_ctor_get(v_mulFn_x3f_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_mulFn_x3f_1198_, 1);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_val_1199_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v_type_1203_; lean_object* v_u_1204_; lean_object* v_semiringInst_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_expectedInst_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1195_);
v_type_1203_ = lean_ctor_get(v_toRing_1197_, 1);
lean_inc_ref_n(v_type_1203_, 3);
v_u_1204_ = lean_ctor_get(v_toRing_1197_, 2);
lean_inc_n(v_u_1204_, 2);
v_semiringInst_1205_ = lean_ctor_get(v_toRing_1197_, 4);
lean_inc_ref(v_semiringInst_1205_);
lean_dec_ref(v_toRing_1197_);
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_u_1204_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_inc_ref(v___x_1208_);
v___x_1209_ = l_Lean_mkConst(v___x_1206_, v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_1211_ = l_Lean_mkConst(v___x_1210_, v___x_1208_);
v___x_1212_ = l_Lean_mkAppB(v___x_1211_, v_type_1203_, v_semiringInst_1205_);
v_expectedInst_1213_ = l_Lean_mkAppB(v___x_1209_, v_type_1203_, v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_1215_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_1216_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1203_, v_u_1204_, v___x_1214_, v___x_1215_, v_expectedInst_1213_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_n(v_a_1217_, 2);
lean_dec_ref_known(v___x_1216_, 1);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1218_, 0, v_a_1217_);
v___x_1219_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1218_, v___y_1180_, v___y_1186_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1219_, 0);
lean_dec(v_unused_1227_);
v___x_1221_ = v___x_1219_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_dec(v___x_1219_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_a_1217_);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1217_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_a_1217_);
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1192_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1192_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_mn_1258_, lean_object* v_acc_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
if (lean_obj_tag(v_mn_1258_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_acc_1259_);
return v___x_1272_;
}
else
{
lean_object* v_p_1273_; lean_object* v_m_1274_; lean_object* v___x_1275_; 
v_p_1273_ = lean_ctor_get(v_mn_1258_, 0);
lean_inc_ref(v_p_1273_);
v_m_1274_ = lean_ctor_get(v_mn_1258_, 1);
lean_inc(v_m_1274_);
lean_dec_ref_known(v_mn_1258_, 2);
v___x_1275_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1273_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_Lean_mkAppB(v_a_1276_, v_acc_1259_, v_a_1278_);
v_mn_1258_ = v_m_1274_;
v_acc_1259_ = v___x_1279_;
goto _start;
}
else
{
lean_dec(v_a_1276_);
lean_dec(v_m_1274_);
lean_dec_ref(v_acc_1259_);
return v___x_1277_;
}
}
else
{
lean_dec(v_m_1274_);
lean_dec_ref(v_p_1273_);
lean_dec_ref(v_acc_1259_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_mn_1281_, lean_object* v_acc_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_mn_1281_, v_acc_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_to_int(v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_mn_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
if (lean_obj_tag(v_mn_1298_) == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1312_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1311_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1312_;
}
else
{
lean_object* v_p_1313_; lean_object* v_m_1314_; lean_object* v___x_1315_; 
v_p_1313_ = lean_ctor_get(v_mn_1298_, 0);
lean_inc_ref(v_p_1313_);
v_m_1314_ = lean_ctor_get(v_mn_1298_, 1);
lean_inc(v_m_1314_);
lean_dec_ref_known(v_mn_1298_, 2);
v___x_1315_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1313_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1314_, v_a_1316_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1317_;
}
else
{
lean_dec(v_m_1314_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mn_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1332_, lean_object* v_mn_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1347_ = lean_int_dec_eq(v_k_1332_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1332_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l_Lean_mkAppB(v_a_1349_, v_a_1351_, v_a_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
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
lean_dec(v_a_1351_);
lean_dec(v_a_1349_);
return v___x_1352_;
}
}
else
{
lean_dec(v_a_1349_);
lean_dec(v_mn_1333_);
return v___x_1350_;
}
}
else
{
lean_dec(v_mn_1333_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1363_, lean_object* v_mn_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1363_, v_mn_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_k_1363_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1378_, lean_object* v_acc_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
if (lean_obj_tag(v_p_1378_) == 0)
{
lean_object* v_k_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1413_; 
v_k_1392_ = lean_ctor_get(v_p_1378_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_p_1378_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1394_ = v_p_1378_;
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_k_1392_);
lean_dec(v_p_1378_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1397_ = lean_int_dec_eq(v_k_1392_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_del_object(v___x_1394_);
v___x_1398_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1392_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v_k_1392_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = l_Lean_mkAppB(v_a_1399_, v_acc_1379_, v_a_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref(v_acc_1379_);
return v___x_1400_;
}
}
else
{
lean_dec(v_k_1392_);
lean_dec_ref(v_acc_1379_);
return v___x_1398_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_k_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_acc_1379_);
v___x_1411_ = v___x_1394_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_acc_1379_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_k_1414_; lean_object* v_v_1415_; lean_object* v_p_1416_; lean_object* v___x_1417_; 
v_k_1414_ = lean_ctor_get(v_p_1378_, 0);
lean_inc(v_k_1414_);
v_v_1415_ = lean_ctor_get(v_p_1378_, 1);
lean_inc(v_v_1415_);
v_p_1416_ = lean_ctor_get(v_p_1378_, 2);
lean_inc_ref(v_p_1416_);
lean_dec_ref_known(v_p_1378_, 3);
v___x_1417_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1414_, v_v_1415_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v_k_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = l_Lean_mkAppB(v_a_1418_, v_acc_1379_, v_a_1420_);
v_p_1378_ = v_p_1416_;
v_acc_1379_ = v___x_1421_;
goto _start;
}
else
{
lean_dec(v_a_1418_);
lean_dec_ref(v_p_1416_);
lean_dec_ref(v_acc_1379_);
return v___x_1419_;
}
}
else
{
lean_dec_ref(v_p_1416_);
lean_dec(v_v_1415_);
lean_dec(v_k_1414_);
lean_dec_ref(v_acc_1379_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1423_, lean_object* v_acc_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1423_, v_acc_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
if (lean_obj_tag(v_p_1438_) == 0)
{
lean_object* v_k_1451_; lean_object* v___x_1452_; 
v_k_1451_ = lean_ctor_get(v_p_1438_, 0);
lean_inc(v_k_1451_);
lean_dec_ref_known(v_p_1438_, 1);
v___x_1452_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1451_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v_k_1451_);
return v___x_1452_;
}
else
{
lean_object* v_k_1453_; lean_object* v_v_1454_; lean_object* v_p_1455_; lean_object* v___x_1456_; 
v_k_1453_ = lean_ctor_get(v_p_1438_, 0);
lean_inc(v_k_1453_);
v_v_1454_ = lean_ctor_get(v_p_1438_, 1);
lean_inc(v_v_1454_);
v_p_1455_ = lean_ctor_get(v_p_1438_, 2);
lean_inc_ref(v_p_1455_);
lean_dec_ref_known(v_p_1438_, 3);
v___x_1456_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1453_, v_v_1454_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v_k_1453_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1455_, v_a_1457_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1458_;
}
else
{
lean_dec_ref(v_p_1455_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1472_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1473_; double v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_float_of_nat(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1478_, lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_ref_1485_; lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1532_; 
v_ref_1485_ = lean_ctor_get(v___y_1482_, 2);
v___x_1486_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1532_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1532_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_traceState_1492_; lean_object* v_env_1493_; lean_object* v_nextMacroScope_1494_; lean_object* v_ngen_1495_; lean_object* v_auxDeclNGen_1496_; lean_object* v_cache_1497_; lean_object* v_recordedDeps_1498_; lean_object* v_messages_1499_; lean_object* v_infoState_1500_; lean_object* v_snapshotTasks_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1531_; 
v___x_1491_ = lean_st_ref_take(v___y_1483_);
v_traceState_1492_ = lean_ctor_get(v___x_1491_, 4);
v_env_1493_ = lean_ctor_get(v___x_1491_, 0);
v_nextMacroScope_1494_ = lean_ctor_get(v___x_1491_, 1);
v_ngen_1495_ = lean_ctor_get(v___x_1491_, 2);
v_auxDeclNGen_1496_ = lean_ctor_get(v___x_1491_, 3);
v_cache_1497_ = lean_ctor_get(v___x_1491_, 5);
v_recordedDeps_1498_ = lean_ctor_get(v___x_1491_, 6);
v_messages_1499_ = lean_ctor_get(v___x_1491_, 7);
v_infoState_1500_ = lean_ctor_get(v___x_1491_, 8);
v_snapshotTasks_1501_ = lean_ctor_get(v___x_1491_, 9);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1503_ = v___x_1491_;
v_isShared_1504_ = v_isSharedCheck_1531_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snapshotTasks_1501_);
lean_inc(v_infoState_1500_);
lean_inc(v_messages_1499_);
lean_inc(v_recordedDeps_1498_);
lean_inc(v_cache_1497_);
lean_inc(v_traceState_1492_);
lean_inc(v_auxDeclNGen_1496_);
lean_inc(v_ngen_1495_);
lean_inc(v_nextMacroScope_1494_);
lean_inc(v_env_1493_);
lean_dec(v___x_1491_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1531_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
uint64_t v_tid_1505_; lean_object* v_traces_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1530_; 
v_tid_1505_ = lean_ctor_get_uint64(v_traceState_1492_, sizeof(void*)*1);
v_traces_1506_ = lean_ctor_get(v_traceState_1492_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_traceState_1492_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1508_ = v_traceState_1492_;
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_traces_1506_);
lean_dec(v_traceState_1492_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; double v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1513_ = 0;
v___x_1514_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1515_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1515_, 0, v_cls_1478_);
lean_ctor_set(v___x_1515_, 1, v___x_1511_);
lean_ctor_set(v___x_1515_, 2, v___x_1514_);
lean_ctor_set_float(v___x_1515_, sizeof(void*)*3, v___x_1512_);
lean_ctor_set_float(v___x_1515_, sizeof(void*)*3 + 8, v___x_1512_);
lean_ctor_set_uint8(v___x_1515_, sizeof(void*)*3 + 16, v___x_1513_);
v___x_1516_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1517_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v_a_1487_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
lean_inc(v_ref_1485_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_ref_1485_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Lean_PersistentArray_push___redArg(v_traces_1506_, v___x_1518_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1519_);
v___x_1521_ = v___x_1508_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1519_);
lean_ctor_set_uint64(v_reuseFailAlloc_1529_, sizeof(void*)*1, v_tid_1505_);
v___x_1521_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v___x_1521_);
v___x_1523_ = v___x_1503_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_env_1493_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_nextMacroScope_1494_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_ngen_1495_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_auxDeclNGen_1496_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_cache_1497_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_recordedDeps_1498_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_messages_1499_);
lean_ctor_set(v_reuseFailAlloc_1528_, 8, v_infoState_1500_);
lean_ctor_set(v_reuseFailAlloc_1528_, 9, v_snapshotTasks_1501_);
v___x_1523_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_st_ref_put(v___y_1483_, v___x_1523_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1510_);
v___x_1526_ = v___x_1489_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1510_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1533_, lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1533_, v_msg_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1556_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1557_ = l_Lean_Name_append(v___x_1556_, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1561_, v_a_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1800_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1800_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1800_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
uint8_t v___x_1578_; 
v___x_1578_ = lean_unbox(v_a_1574_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v___x_1579_ = lean_box(0);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
else
{
lean_object* v___f_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1576_);
lean_inc(v_a_1574_);
v___f_1583_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1583_, 0, v_a_1574_);
v___x_1584_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1791_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1791_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1791_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
if (lean_obj_tag(v_a_1585_) == 1)
{
lean_object* v_val_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1587_);
v_val_1589_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_a_1585_, 1);
v___x_1590_ = 0;
v___x_1591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1591_, 0, v_val_1589_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*1, v___x_1590_);
lean_inc_ref(v_p_1561_);
v___x_1592_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1561_, v_a_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = l_Lean_Meta_Sym_canon(v_a_1593_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = l_Lean_Meta_Sym_shareCommon(v_a_1595_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
lean_inc_ref(v_p_1561_);
v___x_1598_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1561_, v_a_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = lean_unbox(v_a_1574_);
lean_dec(v_a_1574_);
v___x_1601_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1597_, v___x_1600_, v___x_1591_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1746_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1746_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1746_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
if (lean_obj_tag(v_a_1602_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1604_);
v_val_1606_ = lean_ctor_get(v_a_1602_, 0);
lean_inc_n(v_val_1606_, 2);
lean_dec_ref_known(v_a_1602_, 1);
v___x_1607_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_val_1606_, v___x_1591_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1733_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1733_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1733_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
if (lean_obj_tag(v_a_1608_) == 1)
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1728_; 
lean_del_object(v___x_1610_);
v_val_1612_ = lean_ctor_get(v_a_1608_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1608_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1614_ = v_a_1608_;
v_isShared_1615_ = v_isSharedCheck_1728_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v_a_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1728_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; 
lean_inc(v_val_1612_);
v___x_1616_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1612_, v___x_1591_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec_ref_known(v___x_1591_, 1);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1617_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_n(v_a_1619_, 2);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1571_);
lean_inc_ref(v_a_1570_);
lean_inc(v_a_1569_);
lean_inc_ref(v_a_1568_);
lean_inc(v_a_1567_);
lean_inc_ref(v_a_1566_);
lean_inc(v_a_1565_);
lean_inc_ref(v_a_1564_);
lean_inc(v_a_1563_);
lean_inc(v_a_1562_);
v___x_1621_ = lean_grind_internalize(v_a_1619_, v_a_1599_, v___x_1620_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1702_; 
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1703_);
v___x_1623_ = v___x_1621_;
v_isShared_1624_ = v_isSharedCheck_1702_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v___x_1621_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1702_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1619_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1693_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1693_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1693_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
uint8_t v___x_1639_; 
v___x_1639_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1561_, v_a_1626_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1623_);
v___x_1640_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1641_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1640_, v___f_1583_, v_a_1562_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_toCold_1642_; lean_object* v_options_1643_; uint8_t v_hasTrace_1644_; 
lean_dec_ref_known(v___x_1641_, 1);
v_toCold_1642_ = lean_ctor_get(v_a_1570_, 0);
v_options_1643_ = lean_ctor_get(v_toCold_1642_, 2);
v_hasTrace_1644_ = lean_ctor_get_uint8(v_options_1643_, sizeof(void*)*1);
if (v_hasTrace_1644_ == 0)
{
lean_dec_ref(v_p_1561_);
goto v___jp_1630_;
}
else
{
lean_object* v_inheritedTraceOptions_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_inheritedTraceOptions_1645_ = lean_ctor_get(v_toCold_1642_, 11);
v___x_1646_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1647_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1648_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1645_, v_options_1643_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v_p_1561_);
goto v___jp_1630_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1561_, v_a_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
lean_inc(v_a_1626_);
v___x_1651_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1626_, v_a_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1650_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v_a_1652_);
v___x_1656_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1646_, v___x_1655_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
goto v___jp_1630_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_a_1650_);
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
v_a_1665_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1651_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1651_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
v_a_1673_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1649_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1649_);
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
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec_ref(v_p_1561_);
v_a_1681_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1641_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1641_);
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
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v___x_1689_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1689_);
v___x_1691_ = v___x_1623_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
v___jp_1630_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_val_1612_);
lean_ctor_set(v___x_1631_, 1, v_a_1626_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_val_1606_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1632_);
v___x_1634_ = v___x_1614_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1634_);
v___x_1636_ = v___x_1628_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_del_object(v___x_1623_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1694_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1625_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1625_);
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
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_a_1619_);
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1704_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1621_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1621_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec(v_a_1599_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1712_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1618_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1618_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_del_object(v___x_1614_);
lean_dec(v_val_1612_);
lean_dec(v_val_1606_);
lean_dec(v_a_1599_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1720_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1616_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1616_);
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
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec(v_a_1608_);
lean_dec(v_val_1606_);
lean_dec(v_a_1599_);
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v___x_1729_ = lean_box(0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1729_);
v___x_1731_ = v___x_1610_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
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
lean_dec(v_val_1606_);
lean_dec(v_a_1599_);
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1734_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1607_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1607_);
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
else
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec(v_a_1602_);
lean_dec(v_a_1599_);
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v___x_1742_ = lean_box(0);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1742_);
v___x_1744_ = v___x_1604_;
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
lean_dec(v_a_1599_);
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_p_1561_);
v_a_1747_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1601_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1601_);
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
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1597_);
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v_a_1755_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1598_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1598_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
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
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v_a_1763_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1596_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1596_);
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
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v_a_1771_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1594_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1594_);
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
lean_dec_ref_known(v___x_1591_, 1);
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v_a_1779_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1592_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1592_);
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
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec(v_a_1585_);
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v___x_1787_ = lean_box(0);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1787_);
v___x_1789_ = v___x_1587_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
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
lean_dec_ref(v___f_1583_);
lean_dec(v_a_1574_);
lean_dec_ref(v_p_1561_);
v_a_1792_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1584_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1584_);
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
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_p_1561_);
v_a_1801_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1573_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1573_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec(v_a_1810_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1822_, lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1822_, v_msg_1823_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1837_, lean_object* v_msg_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1837_, v_msg_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1852_, lean_object* v_msg_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1853_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1867_, v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1881_;
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
