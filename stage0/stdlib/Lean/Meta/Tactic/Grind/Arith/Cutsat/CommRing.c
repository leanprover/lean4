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
lean_object* v_vars_239_; lean_object* v_varMap_240_; lean_object* v_varsHistory_241_; lean_object* v_natToIntMap_242_; lean_object* v_natDef_243_; lean_object* v_dvds_244_; lean_object* v_lowers_245_; lean_object* v_uppers_246_; lean_object* v_diseqs_247_; lean_object* v_elimEqs_248_; lean_object* v_elimStack_249_; lean_object* v_occurs_250_; lean_object* v_assignment_251_; lean_object* v_nextCnstrId_252_; uint8_t v_caseSplits_253_; lean_object* v_steps_254_; lean_object* v_penalties_255_; lean_object* v_numReorderRequests_256_; lean_object* v_conflict_x3f_257_; lean_object* v_diseqSplits_258_; lean_object* v_divMod_259_; lean_object* v_nonlinearOccs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
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
v_elimStack_249_ = lean_ctor_get(v_s_238_, 10);
v_occurs_250_ = lean_ctor_get(v_s_238_, 11);
v_assignment_251_ = lean_ctor_get(v_s_238_, 12);
v_nextCnstrId_252_ = lean_ctor_get(v_s_238_, 13);
v_caseSplits_253_ = lean_ctor_get_uint8(v_s_238_, sizeof(void*)*21);
v_steps_254_ = lean_ctor_get(v_s_238_, 14);
v_penalties_255_ = lean_ctor_get(v_s_238_, 15);
v_numReorderRequests_256_ = lean_ctor_get(v_s_238_, 16);
v_conflict_x3f_257_ = lean_ctor_get(v_s_238_, 17);
v_diseqSplits_258_ = lean_ctor_get(v_s_238_, 18);
v_divMod_259_ = lean_ctor_get(v_s_238_, 19);
v_nonlinearOccs_260_ = lean_ctor_get(v_s_238_, 20);
v_isSharedCheck_267_ = !lean_is_exclusive(v_s_238_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v_s_238_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_nonlinearOccs_260_);
lean_inc(v_divMod_259_);
lean_inc(v_diseqSplits_258_);
lean_inc(v_conflict_x3f_257_);
lean_inc(v_numReorderRequests_256_);
lean_inc(v_penalties_255_);
lean_inc(v_steps_254_);
lean_inc(v_nextCnstrId_252_);
lean_inc(v_assignment_251_);
lean_inc(v_occurs_250_);
lean_inc(v_elimStack_249_);
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
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_vars_239_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_varMap_240_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_varsHistory_241_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_natToIntMap_242_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_natDef_243_);
lean_ctor_set(v_reuseFailAlloc_266_, 5, v_dvds_244_);
lean_ctor_set(v_reuseFailAlloc_266_, 6, v_lowers_245_);
lean_ctor_set(v_reuseFailAlloc_266_, 7, v_uppers_246_);
lean_ctor_set(v_reuseFailAlloc_266_, 8, v_diseqs_247_);
lean_ctor_set(v_reuseFailAlloc_266_, 9, v_elimEqs_248_);
lean_ctor_set(v_reuseFailAlloc_266_, 10, v_elimStack_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 11, v_occurs_250_);
lean_ctor_set(v_reuseFailAlloc_266_, 12, v_assignment_251_);
lean_ctor_set(v_reuseFailAlloc_266_, 13, v_nextCnstrId_252_);
lean_ctor_set(v_reuseFailAlloc_266_, 14, v_steps_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 15, v_penalties_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 16, v_numReorderRequests_256_);
lean_ctor_set(v_reuseFailAlloc_266_, 17, v_conflict_x3f_257_);
lean_ctor_set(v_reuseFailAlloc_266_, 18, v_diseqSplits_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 19, v_divMod_259_);
lean_ctor_set(v_reuseFailAlloc_266_, 20, v_nonlinearOccs_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_266_, sizeof(void*)*21, v_caseSplits_253_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*21 + 1, v_a_237_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed(lean_object* v_a_268_, lean_object* v_s_269_){
_start:
{
uint8_t v_a_125066__boxed_270_; lean_object* v_res_271_; 
v_a_125066__boxed_270_ = lean_unbox(v_a_268_);
v_res_271_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_125066__boxed_270_, v_s_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_env_279_; uint8_t v___x_280_; lean_object* v_env_281_; lean_object* v___x_282_; lean_object* v_toCold_283_; lean_object* v_mctx_284_; lean_object* v_lctx_285_; lean_object* v_options_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_278_ = lean_st_ref_get(v___y_276_);
v_env_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_env_279_);
lean_dec(v___x_278_);
v___x_280_ = 0;
v_env_281_ = l_Lean_Environment_setRecordingDeps(v_env_279_, v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_274_);
v_toCold_283_ = lean_ctor_get(v___y_275_, 0);
v_mctx_284_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_mctx_284_);
lean_dec(v___x_282_);
v_lctx_285_ = lean_ctor_get(v___y_273_, 2);
v_options_286_ = lean_ctor_get(v_toCold_283_, 2);
lean_inc_ref(v_options_286_);
lean_inc_ref(v_lctx_285_);
v___x_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_287_, 0, v_env_281_);
lean_ctor_set(v___x_287_, 1, v_mctx_284_);
lean_ctor_set(v___x_287_, 2, v_lctx_285_);
lean_ctor_set(v___x_287_, 3, v_options_286_);
v___x_288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_msgData_272_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(lean_object* v_msgData_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_ref_303_; lean_object* v___x_304_; lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_ref_303_ = lean_ctor_get(v___y_300_, 2);
v___x_304_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_ref_303_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_ref_303_);
lean_ctor_set(v___x_309_, 1, v_a_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_type_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
lean_inc_ref(v_type_324_);
v___x_337_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_324_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_350_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_350_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
if (lean_obj_tag(v_a_338_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_344_; 
lean_dec_ref(v_type_324_);
v_val_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_val_342_);
lean_dec_ref_known(v_a_338_, 1);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_val_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_val_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_del_object(v___x_340_);
lean_dec(v_a_338_);
v___x_346_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
v___x_347_ = l_Lean_indentExpr(v_type_324_);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_348_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
return v___x_349_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_type_324_);
v_a_351_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_337_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_type_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(lean_object* v_type_373_, lean_object* v_u_374_, lean_object* v_instDeclName_375_, lean_object* v_declName_376_, lean_object* v_expectedInst_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_390_ = lean_box(0);
lean_inc_n(v_u_374_, 2);
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v_u_374_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_u_374_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v_u_374_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
lean_inc_ref(v___x_393_);
v___x_394_ = l_Lean_mkConst(v_instDeclName_375_, v___x_393_);
lean_inc_ref_n(v_type_373_, 3);
v___x_395_ = l_Lean_mkApp3(v___x_394_, v_type_373_, v_type_373_, v_type_373_);
v___x_396_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_395_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_n(v_a_397_, 2);
lean_dec_ref_known(v___x_396_, 1);
lean_inc(v_declName_376_);
v___x_398_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_376_, v_a_397_, v_expectedInst_377_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = l_Lean_mkConst(v_declName_376_, v___x_393_);
lean_inc_ref_n(v_type_373_, 2);
v___x_400_ = l_Lean_mkApp4(v___x_399_, v_type_373_, v_type_373_, v_type_373_, v_a_397_);
v___x_401_ = l_Lean_Meta_Sym_canon(v___x_400_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_Meta_Sym_shareCommon(v_a_402_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_403_;
}
else
{
return v___x_401_;
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_a_397_);
lean_dec_ref_known(v___x_393_, 2);
lean_dec(v_declName_376_);
lean_dec_ref(v_type_373_);
v_a_404_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_398_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_398_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_393_, 2);
lean_dec_ref(v_expectedInst_377_);
lean_dec(v_declName_376_);
lean_dec_ref(v_type_373_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_type_412_ = _args[0];
lean_object* v_u_413_ = _args[1];
lean_object* v_instDeclName_414_ = _args[2];
lean_object* v_declName_415_ = _args[3];
lean_object* v_expectedInst_416_ = _args[4];
lean_object* v___y_417_ = _args[5];
lean_object* v___y_418_ = _args[6];
lean_object* v___y_419_ = _args[7];
lean_object* v___y_420_ = _args[8];
lean_object* v___y_421_ = _args[9];
lean_object* v___y_422_ = _args[10];
lean_object* v___y_423_ = _args[11];
lean_object* v___y_424_ = _args[12];
lean_object* v___y_425_ = _args[13];
lean_object* v___y_426_ = _args[14];
lean_object* v___y_427_ = _args[15];
lean_object* v___y_428_ = _args[16];
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_412_, v_u_413_, v_instDeclName_414_, v_declName_415_, v_expectedInst_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(lean_object* v_a_430_, lean_object* v_s_431_){
_start:
{
lean_object* v_toRing_432_; lean_object* v_invFn_x3f_433_; lean_object* v_divFn_x3f_434_; lean_object* v_semiringId_x3f_435_; lean_object* v_commSemiringInst_436_; lean_object* v_commRingInst_437_; lean_object* v_noZeroDivInst_x3f_438_; lean_object* v_fieldInst_x3f_439_; lean_object* v_powIdentityInst_x3f_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_472_; 
v_toRing_432_ = lean_ctor_get(v_s_431_, 0);
v_invFn_x3f_433_ = lean_ctor_get(v_s_431_, 1);
v_divFn_x3f_434_ = lean_ctor_get(v_s_431_, 2);
v_semiringId_x3f_435_ = lean_ctor_get(v_s_431_, 3);
v_commSemiringInst_436_ = lean_ctor_get(v_s_431_, 4);
v_commRingInst_437_ = lean_ctor_get(v_s_431_, 5);
v_noZeroDivInst_x3f_438_ = lean_ctor_get(v_s_431_, 6);
v_fieldInst_x3f_439_ = lean_ctor_get(v_s_431_, 7);
v_powIdentityInst_x3f_440_ = lean_ctor_get(v_s_431_, 8);
v_isSharedCheck_472_ = !lean_is_exclusive(v_s_431_);
if (v_isSharedCheck_472_ == 0)
{
v___x_442_ = v_s_431_;
v_isShared_443_ = v_isSharedCheck_472_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_powIdentityInst_x3f_440_);
lean_inc(v_fieldInst_x3f_439_);
lean_inc(v_noZeroDivInst_x3f_438_);
lean_inc(v_commRingInst_437_);
lean_inc(v_commSemiringInst_436_);
lean_inc(v_semiringId_x3f_435_);
lean_inc(v_divFn_x3f_434_);
lean_inc(v_invFn_x3f_433_);
lean_inc(v_toRing_432_);
lean_dec(v_s_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_472_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_id_444_; lean_object* v_type_445_; lean_object* v_u_446_; lean_object* v_ringInst_447_; lean_object* v_semiringInst_448_; lean_object* v_charInst_x3f_449_; uint8_t v_symbolicChar_450_; lean_object* v_mulFn_x3f_451_; lean_object* v_subFn_x3f_452_; lean_object* v_negFn_x3f_453_; lean_object* v_powFn_x3f_454_; lean_object* v_intCastFn_x3f_455_; lean_object* v_natCastFn_x3f_456_; lean_object* v_natSMulFn_x3f_457_; lean_object* v_intSMulFn_x3f_458_; lean_object* v_one_x3f_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_470_; 
v_id_444_ = lean_ctor_get(v_toRing_432_, 0);
v_type_445_ = lean_ctor_get(v_toRing_432_, 1);
v_u_446_ = lean_ctor_get(v_toRing_432_, 2);
v_ringInst_447_ = lean_ctor_get(v_toRing_432_, 3);
v_semiringInst_448_ = lean_ctor_get(v_toRing_432_, 4);
v_charInst_x3f_449_ = lean_ctor_get(v_toRing_432_, 5);
v_symbolicChar_450_ = lean_ctor_get_uint8(v_toRing_432_, sizeof(void*)*16);
v_mulFn_x3f_451_ = lean_ctor_get(v_toRing_432_, 7);
v_subFn_x3f_452_ = lean_ctor_get(v_toRing_432_, 8);
v_negFn_x3f_453_ = lean_ctor_get(v_toRing_432_, 9);
v_powFn_x3f_454_ = lean_ctor_get(v_toRing_432_, 10);
v_intCastFn_x3f_455_ = lean_ctor_get(v_toRing_432_, 11);
v_natCastFn_x3f_456_ = lean_ctor_get(v_toRing_432_, 12);
v_natSMulFn_x3f_457_ = lean_ctor_get(v_toRing_432_, 13);
v_intSMulFn_x3f_458_ = lean_ctor_get(v_toRing_432_, 14);
v_one_x3f_459_ = lean_ctor_get(v_toRing_432_, 15);
v_isSharedCheck_470_ = !lean_is_exclusive(v_toRing_432_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_toRing_432_, 6);
lean_dec(v_unused_471_);
v___x_461_ = v_toRing_432_;
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_one_x3f_459_);
lean_inc(v_intSMulFn_x3f_458_);
lean_inc(v_natSMulFn_x3f_457_);
lean_inc(v_natCastFn_x3f_456_);
lean_inc(v_intCastFn_x3f_455_);
lean_inc(v_powFn_x3f_454_);
lean_inc(v_negFn_x3f_453_);
lean_inc(v_subFn_x3f_452_);
lean_inc(v_mulFn_x3f_451_);
lean_inc(v_charInst_x3f_449_);
lean_inc(v_semiringInst_448_);
lean_inc(v_ringInst_447_);
lean_inc(v_u_446_);
lean_inc(v_type_445_);
lean_inc(v_id_444_);
lean_dec(v_toRing_432_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_430_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 6, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_id_444_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_type_445_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_u_446_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_ringInst_447_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_semiringInst_448_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v_charInst_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_mulFn_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_subFn_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_469_, 9, v_negFn_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_469_, 10, v_powFn_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_469_, 11, v_intCastFn_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_469_, 12, v_natCastFn_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 13, v_natSMulFn_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 14, v_intSMulFn_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_469_, 15, v_one_x3f_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, sizeof(void*)*16, v_symbolicChar_450_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_465_);
v___x_467_ = v___x_442_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_invFn_x3f_433_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_divFn_x3f_434_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_semiringId_x3f_435_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_commSemiringInst_436_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_commRingInst_437_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_noZeroDivInst_x3f_438_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_fieldInst_x3f_439_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_powIdentityInst_x3f_440_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_548_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_548_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_548_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_548_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_toRing_509_; lean_object* v_addFn_x3f_510_; 
v_toRing_509_ = lean_ctor_get(v_a_505_, 0);
lean_inc_ref(v_toRing_509_);
lean_dec(v_a_505_);
v_addFn_x3f_510_ = lean_ctor_get(v_toRing_509_, 6);
if (lean_obj_tag(v_addFn_x3f_510_) == 1)
{
lean_object* v_val_511_; lean_object* v___x_513_; 
lean_inc_ref(v_addFn_x3f_510_);
lean_dec_ref(v_toRing_509_);
v_val_511_ = lean_ctor_get(v_addFn_x3f_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_addFn_x3f_510_, 1);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v_val_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_val_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v_type_515_; lean_object* v_u_516_; lean_object* v_semiringInst_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_expectedInst_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_del_object(v___x_507_);
v_type_515_ = lean_ctor_get(v_toRing_509_, 1);
lean_inc_ref_n(v_type_515_, 3);
v_u_516_ = lean_ctor_get(v_toRing_509_, 2);
lean_inc_n(v_u_516_, 2);
v_semiringInst_517_ = lean_ctor_get(v_toRing_509_, 4);
lean_inc_ref(v_semiringInst_517_);
lean_dec_ref(v_toRing_509_);
v___x_518_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v_u_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
lean_inc_ref(v___x_520_);
v___x_521_ = l_Lean_mkConst(v___x_518_, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6));
v___x_523_ = l_Lean_mkConst(v___x_522_, v___x_520_);
v___x_524_ = l_Lean_mkAppB(v___x_523_, v_type_515_, v_semiringInst_517_);
v_expectedInst_525_ = l_Lean_mkAppB(v___x_521_, v_type_515_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8));
v___x_527_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10));
v___x_528_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_515_, v_u_516_, v___x_526_, v___x_527_, v_expectedInst_525_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 2);
lean_dec_ref_known(v___x_528_, 1);
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_530_, 0, v_a_529_);
v___x_531_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_530_, v___y_492_, v___y_498_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v___x_531_, 0);
lean_dec(v_unused_539_);
v___x_533_ = v___x_531_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_dec(v___x_531_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_a_529_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_529_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_529_);
v_a_540_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_531_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_531_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_504_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_504_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_570_, lean_object* v_u_571_, lean_object* v_instDeclName_572_, lean_object* v_declName_573_, lean_object* v_expectedInst_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v_u_571_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
lean_inc_ref(v___x_588_);
v___x_589_ = l_Lean_mkConst(v_instDeclName_572_, v___x_588_);
lean_inc_ref(v_type_570_);
v___x_590_ = l_Lean_Expr_app___override(v___x_589_, v_type_570_);
v___x_591_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_590_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc_n(v_a_592_, 2);
lean_dec_ref_known(v___x_591_, 1);
lean_inc(v_declName_573_);
v___x_593_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_573_, v_a_592_, v_expectedInst_574_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_594_ = l_Lean_mkConst(v_declName_573_, v___x_588_);
v___x_595_ = l_Lean_mkAppB(v___x_594_, v_type_570_, v_a_592_);
v___x_596_ = l_Lean_Meta_Sym_canon(v___x_595_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l_Lean_Meta_Sym_shareCommon(v_a_597_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_598_;
}
else
{
return v___x_596_;
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_a_592_);
lean_dec_ref_known(v___x_588_, 2);
lean_dec(v_declName_573_);
lean_dec_ref(v_type_570_);
v_a_599_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_593_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_593_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_588_, 2);
lean_dec_ref(v_expectedInst_574_);
lean_dec(v_declName_573_);
lean_dec_ref(v_type_570_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_607_ = _args[0];
lean_object* v_u_608_ = _args[1];
lean_object* v_instDeclName_609_ = _args[2];
lean_object* v_declName_610_ = _args[3];
lean_object* v_expectedInst_611_ = _args[4];
lean_object* v___y_612_ = _args[5];
lean_object* v___y_613_ = _args[6];
lean_object* v___y_614_ = _args[7];
lean_object* v___y_615_ = _args[8];
lean_object* v___y_616_ = _args[9];
lean_object* v___y_617_ = _args[10];
lean_object* v___y_618_ = _args[11];
lean_object* v___y_619_ = _args[12];
lean_object* v___y_620_ = _args[13];
lean_object* v___y_621_ = _args[14];
lean_object* v___y_622_ = _args[15];
lean_object* v___y_623_ = _args[16];
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_607_, v_u_608_, v_instDeclName_609_, v_declName_610_, v_expectedInst_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_625_, lean_object* v_s_626_){
_start:
{
lean_object* v_toRing_627_; lean_object* v_invFn_x3f_628_; lean_object* v_divFn_x3f_629_; lean_object* v_semiringId_x3f_630_; lean_object* v_commSemiringInst_631_; lean_object* v_commRingInst_632_; lean_object* v_noZeroDivInst_x3f_633_; lean_object* v_fieldInst_x3f_634_; lean_object* v_powIdentityInst_x3f_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_667_; 
v_toRing_627_ = lean_ctor_get(v_s_626_, 0);
v_invFn_x3f_628_ = lean_ctor_get(v_s_626_, 1);
v_divFn_x3f_629_ = lean_ctor_get(v_s_626_, 2);
v_semiringId_x3f_630_ = lean_ctor_get(v_s_626_, 3);
v_commSemiringInst_631_ = lean_ctor_get(v_s_626_, 4);
v_commRingInst_632_ = lean_ctor_get(v_s_626_, 5);
v_noZeroDivInst_x3f_633_ = lean_ctor_get(v_s_626_, 6);
v_fieldInst_x3f_634_ = lean_ctor_get(v_s_626_, 7);
v_powIdentityInst_x3f_635_ = lean_ctor_get(v_s_626_, 8);
v_isSharedCheck_667_ = !lean_is_exclusive(v_s_626_);
if (v_isSharedCheck_667_ == 0)
{
v___x_637_ = v_s_626_;
v_isShared_638_ = v_isSharedCheck_667_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_powIdentityInst_x3f_635_);
lean_inc(v_fieldInst_x3f_634_);
lean_inc(v_noZeroDivInst_x3f_633_);
lean_inc(v_commRingInst_632_);
lean_inc(v_commSemiringInst_631_);
lean_inc(v_semiringId_x3f_630_);
lean_inc(v_divFn_x3f_629_);
lean_inc(v_invFn_x3f_628_);
lean_inc(v_toRing_627_);
lean_dec(v_s_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_667_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_id_639_; lean_object* v_type_640_; lean_object* v_u_641_; lean_object* v_ringInst_642_; lean_object* v_semiringInst_643_; lean_object* v_charInst_x3f_644_; uint8_t v_symbolicChar_645_; lean_object* v_addFn_x3f_646_; lean_object* v_mulFn_x3f_647_; lean_object* v_subFn_x3f_648_; lean_object* v_powFn_x3f_649_; lean_object* v_intCastFn_x3f_650_; lean_object* v_natCastFn_x3f_651_; lean_object* v_natSMulFn_x3f_652_; lean_object* v_intSMulFn_x3f_653_; lean_object* v_one_x3f_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_id_639_ = lean_ctor_get(v_toRing_627_, 0);
v_type_640_ = lean_ctor_get(v_toRing_627_, 1);
v_u_641_ = lean_ctor_get(v_toRing_627_, 2);
v_ringInst_642_ = lean_ctor_get(v_toRing_627_, 3);
v_semiringInst_643_ = lean_ctor_get(v_toRing_627_, 4);
v_charInst_x3f_644_ = lean_ctor_get(v_toRing_627_, 5);
v_symbolicChar_645_ = lean_ctor_get_uint8(v_toRing_627_, sizeof(void*)*16);
v_addFn_x3f_646_ = lean_ctor_get(v_toRing_627_, 6);
v_mulFn_x3f_647_ = lean_ctor_get(v_toRing_627_, 7);
v_subFn_x3f_648_ = lean_ctor_get(v_toRing_627_, 8);
v_powFn_x3f_649_ = lean_ctor_get(v_toRing_627_, 10);
v_intCastFn_x3f_650_ = lean_ctor_get(v_toRing_627_, 11);
v_natCastFn_x3f_651_ = lean_ctor_get(v_toRing_627_, 12);
v_natSMulFn_x3f_652_ = lean_ctor_get(v_toRing_627_, 13);
v_intSMulFn_x3f_653_ = lean_ctor_get(v_toRing_627_, 14);
v_one_x3f_654_ = lean_ctor_get(v_toRing_627_, 15);
v_isSharedCheck_665_ = !lean_is_exclusive(v_toRing_627_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_toRing_627_, 9);
lean_dec(v_unused_666_);
v___x_656_ = v_toRing_627_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_one_x3f_654_);
lean_inc(v_intSMulFn_x3f_653_);
lean_inc(v_natSMulFn_x3f_652_);
lean_inc(v_natCastFn_x3f_651_);
lean_inc(v_intCastFn_x3f_650_);
lean_inc(v_powFn_x3f_649_);
lean_inc(v_subFn_x3f_648_);
lean_inc(v_mulFn_x3f_647_);
lean_inc(v_addFn_x3f_646_);
lean_inc(v_charInst_x3f_644_);
lean_inc(v_semiringInst_643_);
lean_inc(v_ringInst_642_);
lean_inc(v_u_641_);
lean_inc(v_type_640_);
lean_inc(v_id_639_);
lean_dec(v_toRing_627_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_a_625_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 9, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_id_639_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_type_640_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_u_641_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_ringInst_642_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_semiringInst_643_);
lean_ctor_set(v_reuseFailAlloc_664_, 5, v_charInst_x3f_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 6, v_addFn_x3f_646_);
lean_ctor_set(v_reuseFailAlloc_664_, 7, v_mulFn_x3f_647_);
lean_ctor_set(v_reuseFailAlloc_664_, 8, v_subFn_x3f_648_);
lean_ctor_set(v_reuseFailAlloc_664_, 9, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_664_, 10, v_powFn_x3f_649_);
lean_ctor_set(v_reuseFailAlloc_664_, 11, v_intCastFn_x3f_650_);
lean_ctor_set(v_reuseFailAlloc_664_, 12, v_natCastFn_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_664_, 13, v_natSMulFn_x3f_652_);
lean_ctor_set(v_reuseFailAlloc_664_, 14, v_intSMulFn_x3f_653_);
lean_ctor_set(v_reuseFailAlloc_664_, 15, v_one_x3f_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*16, v_symbolicChar_645_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_660_);
v___x_662_ = v___x_637_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_invFn_x3f_628_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_divFn_x3f_629_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_semiringId_x3f_630_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v_commSemiringInst_631_);
lean_ctor_set(v_reuseFailAlloc_663_, 5, v_commRingInst_632_);
lean_ctor_set(v_reuseFailAlloc_663_, 6, v_noZeroDivInst_x3f_633_);
lean_ctor_set(v_reuseFailAlloc_663_, 7, v_fieldInst_x3f_634_);
lean_ctor_set(v_reuseFailAlloc_663_, 8, v_powIdentityInst_x3f_635_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_735_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_735_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_735_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_735_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_toRing_699_; lean_object* v_negFn_x3f_700_; 
v_toRing_699_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_toRing_699_);
lean_dec(v_a_695_);
v_negFn_x3f_700_ = lean_ctor_get(v_toRing_699_, 9);
if (lean_obj_tag(v_negFn_x3f_700_) == 1)
{
lean_object* v_val_701_; lean_object* v___x_703_; 
lean_inc_ref(v_negFn_x3f_700_);
lean_dec_ref(v_toRing_699_);
v_val_701_ = lean_ctor_get(v_negFn_x3f_700_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_negFn_x3f_700_, 1);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_val_701_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_val_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v_type_705_; lean_object* v_u_706_; lean_object* v_ringInst_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_expectedInst_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_del_object(v___x_697_);
v_type_705_ = lean_ctor_get(v_toRing_699_, 1);
lean_inc_ref_n(v_type_705_, 2);
v_u_706_ = lean_ctor_get(v_toRing_699_, 2);
lean_inc_n(v_u_706_, 2);
v_ringInst_707_ = lean_ctor_get(v_toRing_699_, 3);
lean_inc_ref(v_ringInst_707_);
lean_dec_ref(v_toRing_699_);
v___x_708_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2));
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v_u_706_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_mkConst(v___x_708_, v___x_710_);
v_expectedInst_712_ = l_Lean_mkAppB(v___x_711_, v_type_705_, v_ringInst_707_);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_714_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_715_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_705_, v_u_706_, v___x_713_, v___x_714_, v_expectedInst_712_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___f_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___f_717_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_717_, 0, v_a_716_);
v___x_718_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_717_, v___y_682_, v___y_688_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_726_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v_a_716_);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_716_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_716_);
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_694_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_694_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_nat_to_int(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_845_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_845_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_845_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_845_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_toRing_789_; lean_object* v_type_790_; lean_object* v_u_791_; lean_object* v_semiringInst_792_; lean_object* v___x_793_; lean_object* v_n_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_ofNatInst_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_toRing_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc_ref(v_toRing_789_);
lean_dec(v_a_785_);
v_type_790_ = lean_ctor_get(v_toRing_789_, 1);
lean_inc_ref_n(v_type_790_, 2);
v_u_791_ = lean_ctor_get(v_toRing_789_, 2);
lean_inc(v_u_791_);
v_semiringInst_792_ = lean_ctor_get(v_toRing_789_, 4);
lean_inc_ref(v_semiringInst_792_);
lean_dec_ref(v_toRing_789_);
v___x_793_ = lean_nat_abs(v_k_771_);
v_n_794_ = l_Lean_mkRawNatLit(v___x_793_);
v___x_795_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v_u_791_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_inc_ref(v___x_797_);
v___x_829_ = l_Lean_mkConst(v___x_795_, v___x_797_);
lean_inc_ref(v_n_794_);
v___x_830_ = l_Lean_mkAppB(v___x_829_, v_type_790_, v_n_794_);
v___x_831_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_830_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
if (lean_obj_tag(v_a_832_) == 1)
{
lean_object* v_val_833_; 
lean_dec_ref(v_semiringInst_792_);
v_val_833_ = lean_ctor_get(v_a_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_a_832_, 1);
v_ofNatInst_799_ = v_val_833_;
v___y_800_ = v___y_772_;
v___y_801_ = v___y_773_;
v___y_802_ = v___y_774_;
v___y_803_ = v___y_775_;
v___y_804_ = v___y_776_;
v___y_805_ = v___y_777_;
v___y_806_ = v___y_778_;
v___y_807_ = v___y_779_;
v___y_808_ = v___y_780_;
v___y_809_ = v___y_781_;
v___y_810_ = v___y_782_;
goto v___jp_798_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_a_832_);
v___x_834_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5));
lean_inc_ref(v___x_797_);
v___x_835_ = l_Lean_mkConst(v___x_834_, v___x_797_);
lean_inc_ref(v_n_794_);
lean_inc_ref(v_type_790_);
v___x_836_ = l_Lean_mkApp3(v___x_835_, v_type_790_, v_semiringInst_792_, v_n_794_);
v_ofNatInst_799_ = v___x_836_;
v___y_800_ = v___y_772_;
v___y_801_ = v___y_773_;
v___y_802_ = v___y_774_;
v___y_803_ = v___y_775_;
v___y_804_ = v___y_776_;
v___y_805_ = v___y_777_;
v___y_806_ = v___y_778_;
v___y_807_ = v___y_779_;
v___y_808_ = v___y_780_;
v___y_809_ = v___y_781_;
v___y_810_ = v___y_782_;
goto v___jp_798_;
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref_known(v___x_797_, 2);
lean_dec_ref(v_n_794_);
lean_dec_ref(v_semiringInst_792_);
lean_dec_ref(v_type_790_);
lean_del_object(v___x_787_);
v_a_837_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_831_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_831_);
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
v___jp_798_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_e_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_811_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_812_ = l_Lean_mkConst(v___x_811_, v___x_797_);
v_e_813_ = l_Lean_mkApp3(v___x_812_, v_type_790_, v_n_794_, v_ofNatInst_799_);
v___x_814_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_815_ = lean_int_dec_lt(v_k_771_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_e_813_);
v___x_817_ = v___x_787_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_e_813_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_819_; 
lean_del_object(v___x_787_);
v___x_819_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Lean_Expr_app___override(v_a_820_, v_e_813_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_dec_ref(v_e_813_);
return v___x_819_;
}
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_784_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_784_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
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
lean_dec(v_k_854_);
return v_res_867_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = l_Lean_Level_ofNat(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_878_, lean_object* v_type_879_, lean_object* v_semiringInst_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_895_ = lean_box(0);
lean_inc(v_u_878_);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v_u_878_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
lean_inc_ref(v___x_896_);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_894_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v_u_878_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
lean_inc_ref(v___x_898_);
v___x_899_ = l_Lean_mkConst(v___x_893_, v___x_898_);
v___x_900_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_879_, 2);
v___x_901_ = l_Lean_mkApp3(v___x_899_, v_type_879_, v___x_900_, v_type_879_);
v___x_902_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_901_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_inst_x27_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc_n(v_a_903_, 2);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_905_ = l_Lean_mkConst(v___x_904_, v___x_896_);
lean_inc_ref(v_type_879_);
v_inst_x27_906_ = l_Lean_mkAppB(v___x_905_, v_type_879_, v_semiringInst_880_);
v___x_907_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_908_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_907_, v_a_903_, v_inst_x27_906_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v___x_908_, 1);
v___x_909_ = l_Lean_mkConst(v___x_907_, v___x_898_);
lean_inc_ref(v_type_879_);
v___x_910_ = l_Lean_mkApp4(v___x_909_, v_type_879_, v___x_900_, v_type_879_, v_a_903_);
v___x_911_ = l_Lean_Meta_Sym_canon(v___x_910_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_Meta_Sym_shareCommon(v_a_912_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_913_;
}
else
{
return v___x_911_;
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_a_903_);
lean_dec_ref_known(v___x_898_, 2);
lean_dec_ref(v_type_879_);
v_a_914_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_908_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_908_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
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
else
{
lean_dec_ref_known(v___x_898_, 2);
lean_dec_ref_known(v___x_896_, 2);
lean_dec_ref(v_semiringInst_880_);
lean_dec_ref(v_type_879_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_922_, lean_object* v_type_923_, lean_object* v_semiringInst_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_922_, v_type_923_, v_semiringInst_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_938_, lean_object* v_s_939_){
_start:
{
lean_object* v_toRing_940_; lean_object* v_invFn_x3f_941_; lean_object* v_divFn_x3f_942_; lean_object* v_semiringId_x3f_943_; lean_object* v_commSemiringInst_944_; lean_object* v_commRingInst_945_; lean_object* v_noZeroDivInst_x3f_946_; lean_object* v_fieldInst_x3f_947_; lean_object* v_powIdentityInst_x3f_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_980_; 
v_toRing_940_ = lean_ctor_get(v_s_939_, 0);
v_invFn_x3f_941_ = lean_ctor_get(v_s_939_, 1);
v_divFn_x3f_942_ = lean_ctor_get(v_s_939_, 2);
v_semiringId_x3f_943_ = lean_ctor_get(v_s_939_, 3);
v_commSemiringInst_944_ = lean_ctor_get(v_s_939_, 4);
v_commRingInst_945_ = lean_ctor_get(v_s_939_, 5);
v_noZeroDivInst_x3f_946_ = lean_ctor_get(v_s_939_, 6);
v_fieldInst_x3f_947_ = lean_ctor_get(v_s_939_, 7);
v_powIdentityInst_x3f_948_ = lean_ctor_get(v_s_939_, 8);
v_isSharedCheck_980_ = !lean_is_exclusive(v_s_939_);
if (v_isSharedCheck_980_ == 0)
{
v___x_950_ = v_s_939_;
v_isShared_951_ = v_isSharedCheck_980_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_powIdentityInst_x3f_948_);
lean_inc(v_fieldInst_x3f_947_);
lean_inc(v_noZeroDivInst_x3f_946_);
lean_inc(v_commRingInst_945_);
lean_inc(v_commSemiringInst_944_);
lean_inc(v_semiringId_x3f_943_);
lean_inc(v_divFn_x3f_942_);
lean_inc(v_invFn_x3f_941_);
lean_inc(v_toRing_940_);
lean_dec(v_s_939_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_980_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_id_952_; lean_object* v_type_953_; lean_object* v_u_954_; lean_object* v_ringInst_955_; lean_object* v_semiringInst_956_; lean_object* v_charInst_x3f_957_; uint8_t v_symbolicChar_958_; lean_object* v_addFn_x3f_959_; lean_object* v_mulFn_x3f_960_; lean_object* v_subFn_x3f_961_; lean_object* v_negFn_x3f_962_; lean_object* v_intCastFn_x3f_963_; lean_object* v_natCastFn_x3f_964_; lean_object* v_natSMulFn_x3f_965_; lean_object* v_intSMulFn_x3f_966_; lean_object* v_one_x3f_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_978_; 
v_id_952_ = lean_ctor_get(v_toRing_940_, 0);
v_type_953_ = lean_ctor_get(v_toRing_940_, 1);
v_u_954_ = lean_ctor_get(v_toRing_940_, 2);
v_ringInst_955_ = lean_ctor_get(v_toRing_940_, 3);
v_semiringInst_956_ = lean_ctor_get(v_toRing_940_, 4);
v_charInst_x3f_957_ = lean_ctor_get(v_toRing_940_, 5);
v_symbolicChar_958_ = lean_ctor_get_uint8(v_toRing_940_, sizeof(void*)*16);
v_addFn_x3f_959_ = lean_ctor_get(v_toRing_940_, 6);
v_mulFn_x3f_960_ = lean_ctor_get(v_toRing_940_, 7);
v_subFn_x3f_961_ = lean_ctor_get(v_toRing_940_, 8);
v_negFn_x3f_962_ = lean_ctor_get(v_toRing_940_, 9);
v_intCastFn_x3f_963_ = lean_ctor_get(v_toRing_940_, 11);
v_natCastFn_x3f_964_ = lean_ctor_get(v_toRing_940_, 12);
v_natSMulFn_x3f_965_ = lean_ctor_get(v_toRing_940_, 13);
v_intSMulFn_x3f_966_ = lean_ctor_get(v_toRing_940_, 14);
v_one_x3f_967_ = lean_ctor_get(v_toRing_940_, 15);
v_isSharedCheck_978_ = !lean_is_exclusive(v_toRing_940_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_toRing_940_, 10);
lean_dec(v_unused_979_);
v___x_969_ = v_toRing_940_;
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_one_x3f_967_);
lean_inc(v_intSMulFn_x3f_966_);
lean_inc(v_natSMulFn_x3f_965_);
lean_inc(v_natCastFn_x3f_964_);
lean_inc(v_intCastFn_x3f_963_);
lean_inc(v_negFn_x3f_962_);
lean_inc(v_subFn_x3f_961_);
lean_inc(v_mulFn_x3f_960_);
lean_inc(v_addFn_x3f_959_);
lean_inc(v_charInst_x3f_957_);
lean_inc(v_semiringInst_956_);
lean_inc(v_ringInst_955_);
lean_inc(v_u_954_);
lean_inc(v_type_953_);
lean_inc(v_id_952_);
lean_dec(v_toRing_940_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_a_938_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 10, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_id_952_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_type_953_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_u_954_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_ringInst_955_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_semiringInst_956_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v_charInst_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 6, v_addFn_x3f_959_);
lean_ctor_set(v_reuseFailAlloc_977_, 7, v_mulFn_x3f_960_);
lean_ctor_set(v_reuseFailAlloc_977_, 8, v_subFn_x3f_961_);
lean_ctor_set(v_reuseFailAlloc_977_, 9, v_negFn_x3f_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 10, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 11, v_intCastFn_x3f_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 12, v_natCastFn_x3f_964_);
lean_ctor_set(v_reuseFailAlloc_977_, 13, v_natSMulFn_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 14, v_intSMulFn_x3f_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 15, v_one_x3f_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*16, v_symbolicChar_958_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_973_);
v___x_975_ = v___x_950_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_invFn_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_divFn_x3f_942_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_semiringId_x3f_943_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_commSemiringInst_944_);
lean_ctor_set(v_reuseFailAlloc_976_, 5, v_commRingInst_945_);
lean_ctor_set(v_reuseFailAlloc_976_, 6, v_noZeroDivInst_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_976_, 7, v_fieldInst_x3f_947_);
lean_ctor_set(v_reuseFailAlloc_976_, 8, v_powIdentityInst_x3f_948_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1027_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1027_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1027_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_toRing_998_; lean_object* v_powFn_x3f_999_; 
v_toRing_998_ = lean_ctor_get(v_a_994_, 0);
lean_inc_ref(v_toRing_998_);
lean_dec(v_a_994_);
v_powFn_x3f_999_ = lean_ctor_get(v_toRing_998_, 10);
if (lean_obj_tag(v_powFn_x3f_999_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1002_; 
lean_inc_ref(v_powFn_x3f_999_);
lean_dec_ref(v_toRing_998_);
v_val_1000_ = lean_ctor_get(v_powFn_x3f_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_powFn_x3f_999_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_val_1000_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_type_1004_; lean_object* v_u_1005_; lean_object* v_semiringInst_1006_; lean_object* v___x_1007_; 
lean_del_object(v___x_996_);
v_type_1004_ = lean_ctor_get(v_toRing_998_, 1);
lean_inc_ref(v_type_1004_);
v_u_1005_ = lean_ctor_get(v_toRing_998_, 2);
lean_inc(v_u_1005_);
v_semiringInst_1006_ = lean_ctor_get(v_toRing_998_, 4);
lean_inc_ref(v_semiringInst_1006_);
lean_dec_ref(v_toRing_998_);
v___x_1007_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1005_, v_type_1004_, v_semiringInst_1006_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_n(v_a_1008_, 2);
lean_dec_ref_known(v___x_1007_, 1);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1009_, 0, v_a_1008_);
v___x_1010_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1009_, v___y_981_, v___y_987_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1018_);
v___x_1012_ = v___x_1010_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_dec(v___x_1010_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_a_1008_);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1008_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_1008_);
v_a_1019_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1010_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_993_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_993_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_x_1062_; lean_object* v_k_1063_; lean_object* v___y_1065_; lean_object* v_a_1066_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_x_1062_ = lean_ctor_get(v_pw_1049_, 0);
lean_inc(v_x_1062_);
v_k_1063_ = lean_ctor_get(v_pw_1049_, 1);
lean_inc(v_k_1063_);
lean_dec_ref(v_pw_1049_);
v___x_1080_ = l_Lean_instInhabitedExpr;
v___x_1081_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_1050_, v___y_1051_, v___y_1059_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1098_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1098_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1098_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_toRingState_1086_; lean_object* v_vars_1087_; lean_object* v_size_1088_; uint8_t v___x_1089_; 
v_toRingState_1086_ = lean_ctor_get(v_a_1082_, 0);
lean_inc_ref(v_toRingState_1086_);
lean_dec(v_a_1082_);
v_vars_1087_ = lean_ctor_get(v_toRingState_1086_, 0);
lean_inc_ref(v_vars_1087_);
lean_dec_ref(v_toRingState_1086_);
v_size_1088_ = lean_ctor_get(v_vars_1087_, 2);
v___x_1089_ = lean_nat_dec_lt(v_x_1062_, v_size_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_dec_ref(v_vars_1087_);
lean_dec(v_x_1062_);
v___x_1090_ = l_outOfBounds___redArg(v___x_1080_);
lean_inc(v___x_1090_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1090_);
v___x_1092_ = v___x_1084_;
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
v___y_1065_ = v___x_1092_;
v_a_1066_ = v___x_1090_;
goto v___jp_1064_;
}
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1080_, v_vars_1087_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec_ref(v_vars_1087_);
lean_inc(v___x_1094_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1094_);
v___x_1096_ = v___x_1084_;
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
v___y_1065_ = v___x_1096_;
v_a_1066_ = v___x_1094_;
goto v___jp_1064_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_k_1063_);
lean_dec(v_x_1062_);
v_a_1099_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1081_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1081_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
v___jp_1064_:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_dec_eq(v_k_1063_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec_ref(v___y_1065_);
v___x_1069_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1079_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = l_Lean_mkNatLit(v_k_1063_);
v___x_1075_ = l_Lean_mkAppB(v_a_1070_, v_a_1066_, v___x_1074_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
lean_dec_ref(v_a_1066_);
lean_dec(v_k_1063_);
return v___x_1069_;
}
}
else
{
lean_dec_ref(v_a_1066_);
lean_dec(v_k_1063_);
return v___y_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_1121_, lean_object* v_s_1122_){
_start:
{
lean_object* v_toRing_1123_; lean_object* v_invFn_x3f_1124_; lean_object* v_divFn_x3f_1125_; lean_object* v_semiringId_x3f_1126_; lean_object* v_commSemiringInst_1127_; lean_object* v_commRingInst_1128_; lean_object* v_noZeroDivInst_x3f_1129_; lean_object* v_fieldInst_x3f_1130_; lean_object* v_powIdentityInst_x3f_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1163_; 
v_toRing_1123_ = lean_ctor_get(v_s_1122_, 0);
v_invFn_x3f_1124_ = lean_ctor_get(v_s_1122_, 1);
v_divFn_x3f_1125_ = lean_ctor_get(v_s_1122_, 2);
v_semiringId_x3f_1126_ = lean_ctor_get(v_s_1122_, 3);
v_commSemiringInst_1127_ = lean_ctor_get(v_s_1122_, 4);
v_commRingInst_1128_ = lean_ctor_get(v_s_1122_, 5);
v_noZeroDivInst_x3f_1129_ = lean_ctor_get(v_s_1122_, 6);
v_fieldInst_x3f_1130_ = lean_ctor_get(v_s_1122_, 7);
v_powIdentityInst_x3f_1131_ = lean_ctor_get(v_s_1122_, 8);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1122_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1133_ = v_s_1122_;
v_isShared_1134_ = v_isSharedCheck_1163_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1131_);
lean_inc(v_fieldInst_x3f_1130_);
lean_inc(v_noZeroDivInst_x3f_1129_);
lean_inc(v_commRingInst_1128_);
lean_inc(v_commSemiringInst_1127_);
lean_inc(v_semiringId_x3f_1126_);
lean_inc(v_divFn_x3f_1125_);
lean_inc(v_invFn_x3f_1124_);
lean_inc(v_toRing_1123_);
lean_dec(v_s_1122_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1163_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_id_1135_; lean_object* v_type_1136_; lean_object* v_u_1137_; lean_object* v_ringInst_1138_; lean_object* v_semiringInst_1139_; lean_object* v_charInst_x3f_1140_; uint8_t v_symbolicChar_1141_; lean_object* v_addFn_x3f_1142_; lean_object* v_subFn_x3f_1143_; lean_object* v_negFn_x3f_1144_; lean_object* v_powFn_x3f_1145_; lean_object* v_intCastFn_x3f_1146_; lean_object* v_natCastFn_x3f_1147_; lean_object* v_natSMulFn_x3f_1148_; lean_object* v_intSMulFn_x3f_1149_; lean_object* v_one_x3f_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1161_; 
v_id_1135_ = lean_ctor_get(v_toRing_1123_, 0);
v_type_1136_ = lean_ctor_get(v_toRing_1123_, 1);
v_u_1137_ = lean_ctor_get(v_toRing_1123_, 2);
v_ringInst_1138_ = lean_ctor_get(v_toRing_1123_, 3);
v_semiringInst_1139_ = lean_ctor_get(v_toRing_1123_, 4);
v_charInst_x3f_1140_ = lean_ctor_get(v_toRing_1123_, 5);
v_symbolicChar_1141_ = lean_ctor_get_uint8(v_toRing_1123_, sizeof(void*)*16);
v_addFn_x3f_1142_ = lean_ctor_get(v_toRing_1123_, 6);
v_subFn_x3f_1143_ = lean_ctor_get(v_toRing_1123_, 8);
v_negFn_x3f_1144_ = lean_ctor_get(v_toRing_1123_, 9);
v_powFn_x3f_1145_ = lean_ctor_get(v_toRing_1123_, 10);
v_intCastFn_x3f_1146_ = lean_ctor_get(v_toRing_1123_, 11);
v_natCastFn_x3f_1147_ = lean_ctor_get(v_toRing_1123_, 12);
v_natSMulFn_x3f_1148_ = lean_ctor_get(v_toRing_1123_, 13);
v_intSMulFn_x3f_1149_ = lean_ctor_get(v_toRing_1123_, 14);
v_one_x3f_1150_ = lean_ctor_get(v_toRing_1123_, 15);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_toRing_1123_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_toRing_1123_, 7);
lean_dec(v_unused_1162_);
v___x_1152_ = v_toRing_1123_;
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_one_x3f_1150_);
lean_inc(v_intSMulFn_x3f_1149_);
lean_inc(v_natSMulFn_x3f_1148_);
lean_inc(v_natCastFn_x3f_1147_);
lean_inc(v_intCastFn_x3f_1146_);
lean_inc(v_powFn_x3f_1145_);
lean_inc(v_negFn_x3f_1144_);
lean_inc(v_subFn_x3f_1143_);
lean_inc(v_addFn_x3f_1142_);
lean_inc(v_charInst_x3f_1140_);
lean_inc(v_semiringInst_1139_);
lean_inc(v_ringInst_1138_);
lean_inc(v_u_1137_);
lean_inc(v_type_1136_);
lean_inc(v_id_1135_);
lean_dec(v_toRing_1123_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1121_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 7, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_id_1135_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_type_1136_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_u_1137_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_ringInst_1138_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_semiringInst_1139_);
lean_ctor_set(v_reuseFailAlloc_1160_, 5, v_charInst_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1160_, 6, v_addFn_x3f_1142_);
lean_ctor_set(v_reuseFailAlloc_1160_, 7, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1160_, 8, v_subFn_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1160_, 9, v_negFn_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1160_, 10, v_powFn_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1160_, 11, v_intCastFn_x3f_1146_);
lean_ctor_set(v_reuseFailAlloc_1160_, 12, v_natCastFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1160_, 13, v_natSMulFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1160_, 14, v_intSMulFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1160_, 15, v_one_x3f_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1160_, sizeof(void*)*16, v_symbolicChar_1141_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1156_);
v___x_1158_ = v___x_1133_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_invFn_x3f_1124_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_divFn_x3f_1125_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_semiringId_x3f_1126_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_commSemiringInst_1127_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_commRingInst_1128_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_noZeroDivInst_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_fieldInst_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_powIdentityInst_x3f_1131_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1231_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1231_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1231_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_toRing_1192_; lean_object* v_mulFn_x3f_1193_; 
v_toRing_1192_ = lean_ctor_get(v_a_1188_, 0);
lean_inc_ref(v_toRing_1192_);
lean_dec(v_a_1188_);
v_mulFn_x3f_1193_ = lean_ctor_get(v_toRing_1192_, 7);
if (lean_obj_tag(v_mulFn_x3f_1193_) == 1)
{
lean_object* v_val_1194_; lean_object* v___x_1196_; 
lean_inc_ref(v_mulFn_x3f_1193_);
lean_dec_ref(v_toRing_1192_);
v_val_1194_ = lean_ctor_get(v_mulFn_x3f_1193_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v_mulFn_x3f_1193_, 1);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v_val_1194_);
v___x_1196_ = v___x_1190_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_val_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v_type_1198_; lean_object* v_u_1199_; lean_object* v_semiringInst_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_expectedInst_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_del_object(v___x_1190_);
v_type_1198_ = lean_ctor_get(v_toRing_1192_, 1);
lean_inc_ref_n(v_type_1198_, 3);
v_u_1199_ = lean_ctor_get(v_toRing_1192_, 2);
lean_inc_n(v_u_1199_, 2);
v_semiringInst_1200_ = lean_ctor_get(v_toRing_1192_, 4);
lean_inc_ref(v_semiringInst_1200_);
lean_dec_ref(v_toRing_1192_);
v___x_1201_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_u_1199_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_inc_ref(v___x_1203_);
v___x_1204_ = l_Lean_mkConst(v___x_1201_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_1206_ = l_Lean_mkConst(v___x_1205_, v___x_1203_);
v___x_1207_ = l_Lean_mkAppB(v___x_1206_, v_type_1198_, v_semiringInst_1200_);
v_expectedInst_1208_ = l_Lean_mkAppB(v___x_1204_, v_type_1198_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_1210_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_1211_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1198_, v_u_1199_, v___x_1209_, v___x_1210_, v_expectedInst_1208_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_n(v_a_1212_, 2);
lean_dec_ref_known(v___x_1211_, 1);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1213_, 0, v_a_1212_);
v___x_1214_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1213_, v___y_1175_, v___y_1181_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1222_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1212_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1212_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1212_);
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1187_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1187_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_mn_1253_, lean_object* v_acc_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
if (lean_obj_tag(v_mn_1253_) == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_acc_1254_);
return v___x_1267_;
}
else
{
lean_object* v_p_1268_; lean_object* v_m_1269_; lean_object* v___x_1270_; 
v_p_1268_ = lean_ctor_get(v_mn_1253_, 0);
lean_inc_ref(v_p_1268_);
v_m_1269_ = lean_ctor_get(v_mn_1253_, 1);
lean_inc(v_m_1269_);
lean_dec_ref_known(v_mn_1253_, 2);
v___x_1270_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1268_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_mkAppB(v_a_1271_, v_acc_1254_, v_a_1273_);
v_mn_1253_ = v_m_1269_;
v_acc_1254_ = v___x_1274_;
goto _start;
}
else
{
lean_dec(v_a_1271_);
lean_dec(v_m_1269_);
lean_dec_ref(v_acc_1254_);
return v___x_1272_;
}
}
else
{
lean_dec(v_m_1269_);
lean_dec_ref(v_p_1268_);
lean_dec_ref(v_acc_1254_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_mn_1276_, lean_object* v_acc_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_mn_1276_, v_acc_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1290_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_to_int(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_mn_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
if (lean_obj_tag(v_mn_1293_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1307_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1306_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1307_;
}
else
{
lean_object* v_p_1308_; lean_object* v_m_1309_; lean_object* v___x_1310_; 
v_p_1308_ = lean_ctor_get(v_mn_1293_, 0);
lean_inc_ref(v_p_1308_);
v_m_1309_ = lean_ctor_get(v_mn_1293_, 1);
lean_inc(v_m_1309_);
lean_dec_ref_known(v_mn_1293_, 2);
v___x_1310_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1308_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1309_, v_a_1311_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1312_;
}
else
{
lean_dec(v_m_1309_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mn_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1327_, lean_object* v_mn_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1342_ = lean_int_dec_eq(v_k_1327_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1327_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1356_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l_Lean_mkAppB(v_a_1344_, v_a_1346_, v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_dec(v_a_1346_);
lean_dec(v_a_1344_);
return v___x_1347_;
}
}
else
{
lean_dec(v_a_1344_);
lean_dec(v_mn_1328_);
return v___x_1345_;
}
}
else
{
lean_dec(v_mn_1328_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1358_, lean_object* v_mn_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1358_, v_mn_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v_k_1358_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1373_, lean_object* v_acc_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
if (lean_obj_tag(v_p_1373_) == 0)
{
lean_object* v_k_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1408_; 
v_k_1387_ = lean_ctor_get(v_p_1373_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_p_1373_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1389_ = v_p_1373_;
v_isShared_1390_ = v_isSharedCheck_1408_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_k_1387_);
lean_dec(v_p_1373_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1408_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1392_ = lean_int_dec_eq(v_k_1387_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1389_);
v___x_1393_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1387_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v_k_1387_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_mkAppB(v_a_1394_, v_acc_1374_, v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_dec(v_a_1394_);
lean_dec_ref(v_acc_1374_);
return v___x_1395_;
}
}
else
{
lean_dec(v_k_1387_);
lean_dec_ref(v_acc_1374_);
return v___x_1393_;
}
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_k_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_acc_1374_);
v___x_1406_ = v___x_1389_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_acc_1374_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v_p_1411_; lean_object* v___x_1412_; 
v_k_1409_ = lean_ctor_get(v_p_1373_, 0);
lean_inc(v_k_1409_);
v_v_1410_ = lean_ctor_get(v_p_1373_, 1);
lean_inc(v_v_1410_);
v_p_1411_ = lean_ctor_get(v_p_1373_, 2);
lean_inc_ref(v_p_1411_);
lean_dec_ref_known(v_p_1373_, 3);
v___x_1412_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1409_, v_v_1410_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v_k_1409_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_mkAppB(v_a_1413_, v_acc_1374_, v_a_1415_);
v_p_1373_ = v_p_1411_;
v_acc_1374_ = v___x_1416_;
goto _start;
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_p_1411_);
lean_dec_ref(v_acc_1374_);
return v___x_1414_;
}
}
else
{
lean_dec_ref(v_p_1411_);
lean_dec(v_v_1410_);
lean_dec(v_k_1409_);
lean_dec_ref(v_acc_1374_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1418_, lean_object* v_acc_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1418_, v_acc_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
if (lean_obj_tag(v_p_1433_) == 0)
{
lean_object* v_k_1446_; lean_object* v___x_1447_; 
v_k_1446_ = lean_ctor_get(v_p_1433_, 0);
lean_inc(v_k_1446_);
lean_dec_ref_known(v_p_1433_, 1);
v___x_1447_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1446_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v_k_1446_);
return v___x_1447_;
}
else
{
lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v_p_1450_; lean_object* v___x_1451_; 
v_k_1448_ = lean_ctor_get(v_p_1433_, 0);
lean_inc(v_k_1448_);
v_v_1449_ = lean_ctor_get(v_p_1433_, 1);
lean_inc(v_v_1449_);
v_p_1450_ = lean_ctor_get(v_p_1433_, 2);
lean_inc_ref(v_p_1450_);
lean_dec_ref_known(v_p_1433_, 3);
v___x_1451_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1448_, v_v_1449_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v_k_1448_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1450_, v_a_1452_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1453_;
}
else
{
lean_dec_ref(v_p_1450_);
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1467_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1468_; double v___x_1469_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_float_of_nat(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1473_, lean_object* v_msg_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_ref_1480_; lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1527_; 
v_ref_1480_ = lean_ctor_get(v___y_1477_, 2);
v___x_1481_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1527_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1527_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v_traceState_1487_; lean_object* v_env_1488_; lean_object* v_nextMacroScope_1489_; lean_object* v_ngen_1490_; lean_object* v_auxDeclNGen_1491_; lean_object* v_cache_1492_; lean_object* v_recordedDeps_1493_; lean_object* v_messages_1494_; lean_object* v_infoState_1495_; lean_object* v_snapshotTasks_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1526_; 
v___x_1486_ = lean_st_ref_take(v___y_1478_);
v_traceState_1487_ = lean_ctor_get(v___x_1486_, 4);
v_env_1488_ = lean_ctor_get(v___x_1486_, 0);
v_nextMacroScope_1489_ = lean_ctor_get(v___x_1486_, 1);
v_ngen_1490_ = lean_ctor_get(v___x_1486_, 2);
v_auxDeclNGen_1491_ = lean_ctor_get(v___x_1486_, 3);
v_cache_1492_ = lean_ctor_get(v___x_1486_, 5);
v_recordedDeps_1493_ = lean_ctor_get(v___x_1486_, 6);
v_messages_1494_ = lean_ctor_get(v___x_1486_, 7);
v_infoState_1495_ = lean_ctor_get(v___x_1486_, 8);
v_snapshotTasks_1496_ = lean_ctor_get(v___x_1486_, 9);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1498_ = v___x_1486_;
v_isShared_1499_ = v_isSharedCheck_1526_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snapshotTasks_1496_);
lean_inc(v_infoState_1495_);
lean_inc(v_messages_1494_);
lean_inc(v_recordedDeps_1493_);
lean_inc(v_cache_1492_);
lean_inc(v_traceState_1487_);
lean_inc(v_auxDeclNGen_1491_);
lean_inc(v_ngen_1490_);
lean_inc(v_nextMacroScope_1489_);
lean_inc(v_env_1488_);
lean_dec(v___x_1486_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1526_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint64_t v_tid_1500_; lean_object* v_traces_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1525_; 
v_tid_1500_ = lean_ctor_get_uint64(v_traceState_1487_, sizeof(void*)*1);
v_traces_1501_ = lean_ctor_get(v_traceState_1487_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_traceState_1487_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1503_ = v_traceState_1487_;
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_traces_1501_);
lean_dec(v_traceState_1487_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; double v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1508_ = 0;
v___x_1509_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1510_, 0, v_cls_1473_);
lean_ctor_set(v___x_1510_, 1, v___x_1506_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
lean_ctor_set_float(v___x_1510_, sizeof(void*)*3, v___x_1507_);
lean_ctor_set_float(v___x_1510_, sizeof(void*)*3 + 8, v___x_1507_);
lean_ctor_set_uint8(v___x_1510_, sizeof(void*)*3 + 16, v___x_1508_);
v___x_1511_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1512_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v_a_1482_);
lean_ctor_set(v___x_1512_, 2, v___x_1511_);
lean_inc(v_ref_1480_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_ref_1480_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_PersistentArray_push___redArg(v_traces_1501_, v___x_1513_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1514_);
v___x_1516_ = v___x_1503_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1514_);
lean_ctor_set_uint64(v_reuseFailAlloc_1524_, sizeof(void*)*1, v_tid_1500_);
v___x_1516_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v___x_1516_);
v___x_1518_ = v___x_1498_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_env_1488_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_nextMacroScope_1489_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_ngen_1490_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_auxDeclNGen_1491_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 5, v_cache_1492_);
lean_ctor_set(v_reuseFailAlloc_1523_, 6, v_recordedDeps_1493_);
lean_ctor_set(v_reuseFailAlloc_1523_, 7, v_messages_1494_);
lean_ctor_set(v_reuseFailAlloc_1523_, 8, v_infoState_1495_);
lean_ctor_set(v_reuseFailAlloc_1523_, 9, v_snapshotTasks_1496_);
v___x_1518_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_st_ref_put(v___y_1478_, v___x_1518_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1505_);
v___x_1521_ = v___x_1484_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1505_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1528_, v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1551_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1552_ = l_Lean_Name_append(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1556_, v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1795_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1795_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1795_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_unbox(v_a_1569_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v___x_1574_ = lean_box(0);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1571_);
lean_inc(v_a_1569_);
v___f_1578_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1578_, 0, v_a_1569_);
v___x_1579_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1786_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1786_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1786_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_del_object(v___x_1582_);
v_val_1584_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_a_1580_, 1);
v___x_1585_ = 0;
v___x_1586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1586_, 0, v_val_1584_);
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*1, v___x_1585_);
lean_inc_ref(v_p_1556_);
v___x_1587_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1556_, v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Meta_Sym_canon(v_a_1588_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Meta_Sym_shareCommon(v_a_1590_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
lean_inc_ref(v_p_1556_);
v___x_1593_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1556_, v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = lean_unbox(v_a_1569_);
lean_dec(v_a_1569_);
v___x_1596_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1592_, v___x_1595_, v___x_1586_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1741_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1741_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1741_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
if (lean_obj_tag(v_a_1597_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1599_);
v_val_1601_ = lean_ctor_get(v_a_1597_, 0);
lean_inc_n(v_val_1601_, 2);
lean_dec_ref_known(v_a_1597_, 1);
v___x_1602_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_val_1601_, v___x_1586_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1728_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1728_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1728_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
if (lean_obj_tag(v_a_1603_) == 1)
{
lean_object* v_val_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1723_; 
lean_del_object(v___x_1605_);
v_val_1607_ = lean_ctor_get(v_a_1603_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1609_ = v_a_1603_;
v_isShared_1610_ = v_isSharedCheck_1723_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_val_1607_);
lean_dec(v_a_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1723_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; 
lean_inc(v_val_1607_);
v___x_1611_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1607_, v___x_1586_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec_ref_known(v___x_1586_, 1);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1612_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_n(v_a_1614_, 2);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
lean_inc(v_a_1558_);
lean_inc(v_a_1557_);
v___x_1616_ = lean_grind_internalize(v_a_1614_, v_a_1594_, v___x_1615_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1697_; 
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1698_);
v___x_1618_ = v___x_1616_;
v_isShared_1619_ = v_isSharedCheck_1697_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1616_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1697_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1614_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1688_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1688_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1688_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
uint8_t v___x_1634_; 
v___x_1634_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1556_, v_a_1621_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_del_object(v___x_1618_);
v___x_1635_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1636_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1635_, v___f_1578_, v_a_1557_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_toCold_1637_; lean_object* v_options_1638_; uint8_t v_hasTrace_1639_; 
lean_dec_ref_known(v___x_1636_, 1);
v_toCold_1637_ = lean_ctor_get(v_a_1565_, 0);
v_options_1638_ = lean_ctor_get(v_toCold_1637_, 2);
v_hasTrace_1639_ = lean_ctor_get_uint8(v_options_1638_, sizeof(void*)*1);
if (v_hasTrace_1639_ == 0)
{
lean_dec_ref(v_p_1556_);
goto v___jp_1625_;
}
else
{
lean_object* v_inheritedTraceOptions_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_inheritedTraceOptions_1640_ = lean_ctor_get(v_toCold_1637_, 11);
v___x_1641_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1642_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1640_, v_options_1638_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_dec_ref(v_p_1556_);
goto v___jp_1625_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1556_, v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
lean_inc(v_a_1621_);
v___x_1646_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1621_, v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_a_1645_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_a_1647_);
v___x_1651_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1641_, v___x_1650_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_dec_ref_known(v___x_1651_, 1);
goto v___jp_1625_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1645_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
v_a_1660_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1646_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1646_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
v_a_1668_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1644_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1644_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec_ref(v_p_1556_);
v_a_1676_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1636_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1636_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v___x_1684_ = lean_box(0);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1684_);
v___x_1686_ = v___x_1618_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
v___jp_1625_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_val_1607_);
lean_ctor_set(v___x_1626_, 1, v_a_1621_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_val_1601_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1627_);
v___x_1629_ = v___x_1609_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1629_);
v___x_1631_ = v___x_1623_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1618_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1689_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1620_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1620_);
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
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1614_);
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1699_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1616_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1616_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec(v_a_1594_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1707_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1613_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1613_);
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
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_del_object(v___x_1609_);
lean_dec(v_val_1607_);
lean_dec(v_val_1601_);
lean_dec(v_a_1594_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1715_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1611_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1611_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec(v_a_1603_);
lean_dec(v_val_1601_);
lean_dec(v_a_1594_);
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v___x_1724_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1724_);
v___x_1726_ = v___x_1605_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_val_1601_);
lean_dec(v_a_1594_);
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1729_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1602_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1602_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec(v_a_1597_);
lean_dec(v_a_1594_);
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v___x_1737_ = lean_box(0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1737_);
v___x_1739_ = v___x_1599_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
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
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_a_1594_);
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_p_1556_);
v_a_1742_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1596_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1596_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
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
lean_dec(v_a_1592_);
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v_a_1750_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1593_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1593_);
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
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v_a_1758_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1591_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1591_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v_a_1766_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1589_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1589_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v_a_1774_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1587_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1587_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
lean_dec(v_a_1580_);
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v___x_1782_ = lean_box(0);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1782_);
v___x_1784_ = v___x_1582_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
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
lean_dec_ref(v___f_1578_);
lean_dec(v_a_1569_);
lean_dec_ref(v_p_1556_);
v_a_1787_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1579_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1579_);
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
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_p_1556_);
v_a_1796_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1568_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1568_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec(v_a_1805_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1817_, lean_object* v_msg_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1817_, v_msg_1818_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1832_, lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1832_, v_msg_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1848_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1862_, lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1862_, v_msg_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1876_;
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
