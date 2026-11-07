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
uint8_t v_a_125295__boxed_270_; lean_object* v_res_271_; 
v_a_125295__boxed_270_ = lean_unbox(v_a_268_);
v_res_271_ = l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0(v_a_125295__boxed_270_, v_s_269_);
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
lean_object* v_toRing_432_; lean_object* v_invFn_x3f_433_; lean_object* v_divFn_x3f_434_; lean_object* v_zpowFn_x3f_435_; lean_object* v_semiringId_x3f_436_; lean_object* v_commSemiringInst_437_; lean_object* v_commRingInst_438_; lean_object* v_noZeroDivInst_x3f_439_; lean_object* v_fieldInst_x3f_440_; lean_object* v_powIdentityInst_x3f_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_473_; 
v_toRing_432_ = lean_ctor_get(v_s_431_, 0);
v_invFn_x3f_433_ = lean_ctor_get(v_s_431_, 1);
v_divFn_x3f_434_ = lean_ctor_get(v_s_431_, 2);
v_zpowFn_x3f_435_ = lean_ctor_get(v_s_431_, 3);
v_semiringId_x3f_436_ = lean_ctor_get(v_s_431_, 4);
v_commSemiringInst_437_ = lean_ctor_get(v_s_431_, 5);
v_commRingInst_438_ = lean_ctor_get(v_s_431_, 6);
v_noZeroDivInst_x3f_439_ = lean_ctor_get(v_s_431_, 7);
v_fieldInst_x3f_440_ = lean_ctor_get(v_s_431_, 8);
v_powIdentityInst_x3f_441_ = lean_ctor_get(v_s_431_, 9);
v_isSharedCheck_473_ = !lean_is_exclusive(v_s_431_);
if (v_isSharedCheck_473_ == 0)
{
v___x_443_ = v_s_431_;
v_isShared_444_ = v_isSharedCheck_473_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_powIdentityInst_x3f_441_);
lean_inc(v_fieldInst_x3f_440_);
lean_inc(v_noZeroDivInst_x3f_439_);
lean_inc(v_commRingInst_438_);
lean_inc(v_commSemiringInst_437_);
lean_inc(v_semiringId_x3f_436_);
lean_inc(v_zpowFn_x3f_435_);
lean_inc(v_divFn_x3f_434_);
lean_inc(v_invFn_x3f_433_);
lean_inc(v_toRing_432_);
lean_dec(v_s_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_473_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_id_445_; lean_object* v_type_446_; lean_object* v_u_447_; lean_object* v_ringInst_448_; lean_object* v_semiringInst_449_; lean_object* v_charInst_x3f_450_; uint8_t v_symbolicChar_451_; lean_object* v_mulFn_x3f_452_; lean_object* v_subFn_x3f_453_; lean_object* v_negFn_x3f_454_; lean_object* v_powFn_x3f_455_; lean_object* v_intCastFn_x3f_456_; lean_object* v_natCastFn_x3f_457_; lean_object* v_natSMulFn_x3f_458_; lean_object* v_intSMulFn_x3f_459_; lean_object* v_one_x3f_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_471_; 
v_id_445_ = lean_ctor_get(v_toRing_432_, 0);
v_type_446_ = lean_ctor_get(v_toRing_432_, 1);
v_u_447_ = lean_ctor_get(v_toRing_432_, 2);
v_ringInst_448_ = lean_ctor_get(v_toRing_432_, 3);
v_semiringInst_449_ = lean_ctor_get(v_toRing_432_, 4);
v_charInst_x3f_450_ = lean_ctor_get(v_toRing_432_, 5);
v_symbolicChar_451_ = lean_ctor_get_uint8(v_toRing_432_, sizeof(void*)*16);
v_mulFn_x3f_452_ = lean_ctor_get(v_toRing_432_, 7);
v_subFn_x3f_453_ = lean_ctor_get(v_toRing_432_, 8);
v_negFn_x3f_454_ = lean_ctor_get(v_toRing_432_, 9);
v_powFn_x3f_455_ = lean_ctor_get(v_toRing_432_, 10);
v_intCastFn_x3f_456_ = lean_ctor_get(v_toRing_432_, 11);
v_natCastFn_x3f_457_ = lean_ctor_get(v_toRing_432_, 12);
v_natSMulFn_x3f_458_ = lean_ctor_get(v_toRing_432_, 13);
v_intSMulFn_x3f_459_ = lean_ctor_get(v_toRing_432_, 14);
v_one_x3f_460_ = lean_ctor_get(v_toRing_432_, 15);
v_isSharedCheck_471_ = !lean_is_exclusive(v_toRing_432_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_toRing_432_, 6);
lean_dec(v_unused_472_);
v___x_462_ = v_toRing_432_;
v_isShared_463_ = v_isSharedCheck_471_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_one_x3f_460_);
lean_inc(v_intSMulFn_x3f_459_);
lean_inc(v_natSMulFn_x3f_458_);
lean_inc(v_natCastFn_x3f_457_);
lean_inc(v_intCastFn_x3f_456_);
lean_inc(v_powFn_x3f_455_);
lean_inc(v_negFn_x3f_454_);
lean_inc(v_subFn_x3f_453_);
lean_inc(v_mulFn_x3f_452_);
lean_inc(v_charInst_x3f_450_);
lean_inc(v_semiringInst_449_);
lean_inc(v_ringInst_448_);
lean_inc(v_u_447_);
lean_inc(v_type_446_);
lean_inc(v_id_445_);
lean_dec(v_toRing_432_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_471_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v_a_430_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 6, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_id_445_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_type_446_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_u_447_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_ringInst_448_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_semiringInst_449_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_charInst_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_470_, 6, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 7, v_mulFn_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_subFn_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_470_, 9, v_negFn_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 10, v_powFn_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 11, v_intCastFn_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_470_, 12, v_natCastFn_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_470_, 13, v_natSMulFn_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_470_, 14, v_intSMulFn_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_470_, 15, v_one_x3f_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, sizeof(void*)*16, v_symbolicChar_451_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_466_);
v___x_468_ = v___x_443_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_invFn_x3f_433_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_divFn_x3f_434_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_zpowFn_x3f_435_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_semiringId_x3f_436_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v_commSemiringInst_437_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_commRingInst_438_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_noZeroDivInst_x3f_439_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_fieldInst_x3f_440_);
lean_ctor_set(v_reuseFailAlloc_469_, 9, v_powIdentityInst_x3f_441_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_549_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_549_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_549_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_549_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_toRing_510_; lean_object* v_addFn_x3f_511_; 
v_toRing_510_ = lean_ctor_get(v_a_506_, 0);
lean_inc_ref(v_toRing_510_);
lean_dec(v_a_506_);
v_addFn_x3f_511_ = lean_ctor_get(v_toRing_510_, 6);
if (lean_obj_tag(v_addFn_x3f_511_) == 1)
{
lean_object* v_val_512_; lean_object* v___x_514_; 
lean_inc_ref(v_addFn_x3f_511_);
lean_dec_ref(v_toRing_510_);
v_val_512_ = lean_ctor_get(v_addFn_x3f_511_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_addFn_x3f_511_, 1);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_val_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_val_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
lean_object* v_type_516_; lean_object* v_u_517_; lean_object* v_semiringInst_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_expectedInst_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_del_object(v___x_508_);
v_type_516_ = lean_ctor_get(v_toRing_510_, 1);
lean_inc_ref_n(v_type_516_, 3);
v_u_517_ = lean_ctor_get(v_toRing_510_, 2);
lean_inc_n(v_u_517_, 2);
v_semiringInst_518_ = lean_ctor_get(v_toRing_510_, 4);
lean_inc_ref(v_semiringInst_518_);
lean_dec_ref(v_toRing_510_);
v___x_519_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1));
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_521_, 0, v_u_517_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
lean_inc_ref(v___x_521_);
v___x_522_ = l_Lean_mkConst(v___x_519_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6));
v___x_524_ = l_Lean_mkConst(v___x_523_, v___x_521_);
v___x_525_ = l_Lean_mkAppB(v___x_524_, v_type_516_, v_semiringInst_518_);
v_expectedInst_526_ = l_Lean_mkAppB(v___x_522_, v_type_516_, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__8));
v___x_528_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__10));
v___x_529_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_516_, v_u_517_, v___x_527_, v___x_528_, v_expectedInst_526_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_n(v_a_530_, 2);
lean_dec_ref_known(v___x_529_, 1);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_531_, 0, v_a_530_);
v___x_532_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_531_, v___y_493_, v___y_499_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_532_, 0);
lean_dec(v_unused_540_);
v___x_534_ = v___x_532_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v___x_532_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_a_530_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_530_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_530_);
v_a_541_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_532_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_532_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_505_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_505_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_type_571_, lean_object* v_u_572_, lean_object* v_instDeclName_573_, lean_object* v_declName_574_, lean_object* v_expectedInst_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v_u_572_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
lean_inc_ref(v___x_589_);
v___x_590_ = l_Lean_mkConst(v_instDeclName_573_, v___x_589_);
lean_inc_ref(v_type_571_);
v___x_591_ = l_Lean_Expr_app___override(v___x_590_, v_type_571_);
v___x_592_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_591_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_n(v_a_593_, 2);
lean_dec_ref_known(v___x_592_, 1);
lean_inc(v_declName_574_);
v___x_594_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_574_, v_a_593_, v_expectedInst_575_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_595_ = l_Lean_mkConst(v_declName_574_, v___x_589_);
v___x_596_ = l_Lean_mkAppB(v___x_595_, v_type_571_, v_a_593_);
v___x_597_ = l_Lean_Meta_Sym_canon(v___x_596_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_Meta_Sym_shareCommon(v_a_598_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_599_;
}
else
{
return v___x_597_;
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_a_593_);
lean_dec_ref_known(v___x_589_, 2);
lean_dec(v_declName_574_);
lean_dec_ref(v_type_571_);
v_a_600_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_594_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_594_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_589_, 2);
lean_dec_ref(v_expectedInst_575_);
lean_dec(v_declName_574_);
lean_dec_ref(v_type_571_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_type_608_ = _args[0];
lean_object* v_u_609_ = _args[1];
lean_object* v_instDeclName_610_ = _args[2];
lean_object* v_declName_611_ = _args[3];
lean_object* v_expectedInst_612_ = _args[4];
lean_object* v___y_613_ = _args[5];
lean_object* v___y_614_ = _args[6];
lean_object* v___y_615_ = _args[7];
lean_object* v___y_616_ = _args[8];
lean_object* v___y_617_ = _args[9];
lean_object* v___y_618_ = _args[10];
lean_object* v___y_619_ = _args[11];
lean_object* v___y_620_ = _args[12];
lean_object* v___y_621_ = _args[13];
lean_object* v___y_622_ = _args[14];
lean_object* v___y_623_ = _args[15];
lean_object* v___y_624_ = _args[16];
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_608_, v_u_609_, v_instDeclName_610_, v_declName_611_, v_expectedInst_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_626_, lean_object* v_s_627_){
_start:
{
lean_object* v_toRing_628_; lean_object* v_invFn_x3f_629_; lean_object* v_divFn_x3f_630_; lean_object* v_zpowFn_x3f_631_; lean_object* v_semiringId_x3f_632_; lean_object* v_commSemiringInst_633_; lean_object* v_commRingInst_634_; lean_object* v_noZeroDivInst_x3f_635_; lean_object* v_fieldInst_x3f_636_; lean_object* v_powIdentityInst_x3f_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_669_; 
v_toRing_628_ = lean_ctor_get(v_s_627_, 0);
v_invFn_x3f_629_ = lean_ctor_get(v_s_627_, 1);
v_divFn_x3f_630_ = lean_ctor_get(v_s_627_, 2);
v_zpowFn_x3f_631_ = lean_ctor_get(v_s_627_, 3);
v_semiringId_x3f_632_ = lean_ctor_get(v_s_627_, 4);
v_commSemiringInst_633_ = lean_ctor_get(v_s_627_, 5);
v_commRingInst_634_ = lean_ctor_get(v_s_627_, 6);
v_noZeroDivInst_x3f_635_ = lean_ctor_get(v_s_627_, 7);
v_fieldInst_x3f_636_ = lean_ctor_get(v_s_627_, 8);
v_powIdentityInst_x3f_637_ = lean_ctor_get(v_s_627_, 9);
v_isSharedCheck_669_ = !lean_is_exclusive(v_s_627_);
if (v_isSharedCheck_669_ == 0)
{
v___x_639_ = v_s_627_;
v_isShared_640_ = v_isSharedCheck_669_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_powIdentityInst_x3f_637_);
lean_inc(v_fieldInst_x3f_636_);
lean_inc(v_noZeroDivInst_x3f_635_);
lean_inc(v_commRingInst_634_);
lean_inc(v_commSemiringInst_633_);
lean_inc(v_semiringId_x3f_632_);
lean_inc(v_zpowFn_x3f_631_);
lean_inc(v_divFn_x3f_630_);
lean_inc(v_invFn_x3f_629_);
lean_inc(v_toRing_628_);
lean_dec(v_s_627_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_669_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_id_641_; lean_object* v_type_642_; lean_object* v_u_643_; lean_object* v_ringInst_644_; lean_object* v_semiringInst_645_; lean_object* v_charInst_x3f_646_; uint8_t v_symbolicChar_647_; lean_object* v_addFn_x3f_648_; lean_object* v_mulFn_x3f_649_; lean_object* v_subFn_x3f_650_; lean_object* v_powFn_x3f_651_; lean_object* v_intCastFn_x3f_652_; lean_object* v_natCastFn_x3f_653_; lean_object* v_natSMulFn_x3f_654_; lean_object* v_intSMulFn_x3f_655_; lean_object* v_one_x3f_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_667_; 
v_id_641_ = lean_ctor_get(v_toRing_628_, 0);
v_type_642_ = lean_ctor_get(v_toRing_628_, 1);
v_u_643_ = lean_ctor_get(v_toRing_628_, 2);
v_ringInst_644_ = lean_ctor_get(v_toRing_628_, 3);
v_semiringInst_645_ = lean_ctor_get(v_toRing_628_, 4);
v_charInst_x3f_646_ = lean_ctor_get(v_toRing_628_, 5);
v_symbolicChar_647_ = lean_ctor_get_uint8(v_toRing_628_, sizeof(void*)*16);
v_addFn_x3f_648_ = lean_ctor_get(v_toRing_628_, 6);
v_mulFn_x3f_649_ = lean_ctor_get(v_toRing_628_, 7);
v_subFn_x3f_650_ = lean_ctor_get(v_toRing_628_, 8);
v_powFn_x3f_651_ = lean_ctor_get(v_toRing_628_, 10);
v_intCastFn_x3f_652_ = lean_ctor_get(v_toRing_628_, 11);
v_natCastFn_x3f_653_ = lean_ctor_get(v_toRing_628_, 12);
v_natSMulFn_x3f_654_ = lean_ctor_get(v_toRing_628_, 13);
v_intSMulFn_x3f_655_ = lean_ctor_get(v_toRing_628_, 14);
v_one_x3f_656_ = lean_ctor_get(v_toRing_628_, 15);
v_isSharedCheck_667_ = !lean_is_exclusive(v_toRing_628_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_toRing_628_, 9);
lean_dec(v_unused_668_);
v___x_658_ = v_toRing_628_;
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_one_x3f_656_);
lean_inc(v_intSMulFn_x3f_655_);
lean_inc(v_natSMulFn_x3f_654_);
lean_inc(v_natCastFn_x3f_653_);
lean_inc(v_intCastFn_x3f_652_);
lean_inc(v_powFn_x3f_651_);
lean_inc(v_subFn_x3f_650_);
lean_inc(v_mulFn_x3f_649_);
lean_inc(v_addFn_x3f_648_);
lean_inc(v_charInst_x3f_646_);
lean_inc(v_semiringInst_645_);
lean_inc(v_ringInst_644_);
lean_inc(v_u_643_);
lean_inc(v_type_642_);
lean_inc(v_id_641_);
lean_dec(v_toRing_628_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v_a_626_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 9, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_id_641_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_type_642_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_u_643_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_ringInst_644_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v_semiringInst_645_);
lean_ctor_set(v_reuseFailAlloc_666_, 5, v_charInst_x3f_646_);
lean_ctor_set(v_reuseFailAlloc_666_, 6, v_addFn_x3f_648_);
lean_ctor_set(v_reuseFailAlloc_666_, 7, v_mulFn_x3f_649_);
lean_ctor_set(v_reuseFailAlloc_666_, 8, v_subFn_x3f_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 9, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_666_, 10, v_powFn_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_666_, 11, v_intCastFn_x3f_652_);
lean_ctor_set(v_reuseFailAlloc_666_, 12, v_natCastFn_x3f_653_);
lean_ctor_set(v_reuseFailAlloc_666_, 13, v_natSMulFn_x3f_654_);
lean_ctor_set(v_reuseFailAlloc_666_, 14, v_intSMulFn_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_666_, 15, v_one_x3f_656_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*16, v_symbolicChar_647_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_662_);
v___x_664_ = v___x_639_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_invFn_x3f_629_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_divFn_x3f_630_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_zpowFn_x3f_631_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_semiringId_x3f_632_);
lean_ctor_set(v_reuseFailAlloc_665_, 5, v_commSemiringInst_633_);
lean_ctor_set(v_reuseFailAlloc_665_, 6, v_commRingInst_634_);
lean_ctor_set(v_reuseFailAlloc_665_, 7, v_noZeroDivInst_x3f_635_);
lean_ctor_set(v_reuseFailAlloc_665_, 8, v_fieldInst_x3f_636_);
lean_ctor_set(v_reuseFailAlloc_665_, 9, v_powIdentityInst_x3f_637_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_737_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_737_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_737_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_737_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_toRing_701_; lean_object* v_negFn_x3f_702_; 
v_toRing_701_ = lean_ctor_get(v_a_697_, 0);
lean_inc_ref(v_toRing_701_);
lean_dec(v_a_697_);
v_negFn_x3f_702_ = lean_ctor_get(v_toRing_701_, 9);
if (lean_obj_tag(v_negFn_x3f_702_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_705_; 
lean_inc_ref(v_negFn_x3f_702_);
lean_dec_ref(v_toRing_701_);
v_val_703_ = lean_ctor_get(v_negFn_x3f_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_negFn_x3f_702_, 1);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v_val_703_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v_type_707_; lean_object* v_u_708_; lean_object* v_ringInst_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_expectedInst_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_699_);
v_type_707_ = lean_ctor_get(v_toRing_701_, 1);
lean_inc_ref_n(v_type_707_, 2);
v_u_708_ = lean_ctor_get(v_toRing_701_, 2);
lean_inc_n(v_u_708_, 2);
v_ringInst_709_ = lean_ctor_get(v_toRing_701_, 3);
lean_inc_ref(v_ringInst_709_);
lean_dec_ref(v_toRing_701_);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2));
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_712_, 0, v_u_708_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_mkConst(v___x_710_, v___x_712_);
v_expectedInst_714_ = l_Lean_mkAppB(v___x_713_, v_type_707_, v_ringInst_709_);
v___x_715_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4));
v___x_716_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6));
v___x_717_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_707_, v_u_708_, v___x_715_, v___x_716_, v_expectedInst_714_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___f_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_n(v_a_718_, 2);
lean_dec_ref_known(v___x_717_, 1);
v___f_719_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_719_, 0, v_a_718_);
v___x_720_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_719_, v___y_684_, v___y_690_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_728_);
v___x_722_ = v___x_720_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_dec(v___x_720_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_a_718_);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_718_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_a_718_);
v_a_729_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_720_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_720_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_696_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_696_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_nat_to_int(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(lean_object* v_k_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_847_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_847_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_847_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_847_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_toRing_791_; lean_object* v_type_792_; lean_object* v_u_793_; lean_object* v_semiringInst_794_; lean_object* v___x_795_; lean_object* v_n_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_ofNatInst_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_toRing_791_ = lean_ctor_get(v_a_787_, 0);
lean_inc_ref(v_toRing_791_);
lean_dec(v_a_787_);
v_type_792_ = lean_ctor_get(v_toRing_791_, 1);
lean_inc_ref_n(v_type_792_, 2);
v_u_793_ = lean_ctor_get(v_toRing_791_, 2);
lean_inc(v_u_793_);
v_semiringInst_794_ = lean_ctor_get(v_toRing_791_, 4);
lean_inc_ref(v_semiringInst_794_);
lean_dec_ref(v_toRing_791_);
v___x_795_ = lean_nat_abs(v_k_773_);
v_n_796_ = l_Lean_mkRawNatLit(v___x_795_);
v___x_797_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1));
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v_u_793_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
lean_inc_ref(v___x_799_);
v___x_831_ = l_Lean_mkConst(v___x_797_, v___x_799_);
lean_inc_ref(v_n_796_);
v___x_832_ = l_Lean_mkAppB(v___x_831_, v_type_792_, v_n_796_);
v___x_833_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_832_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
if (lean_obj_tag(v_a_834_) == 1)
{
lean_object* v_val_835_; 
lean_dec_ref(v_semiringInst_794_);
v_val_835_ = lean_ctor_get(v_a_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_a_834_, 1);
v_ofNatInst_801_ = v_val_835_;
v___y_802_ = v___y_774_;
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
goto v___jp_800_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_a_834_);
v___x_836_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5));
lean_inc_ref(v___x_799_);
v___x_837_ = l_Lean_mkConst(v___x_836_, v___x_799_);
lean_inc_ref(v_n_796_);
lean_inc_ref(v_type_792_);
v___x_838_ = l_Lean_mkApp3(v___x_837_, v_type_792_, v_semiringInst_794_, v_n_796_);
v_ofNatInst_801_ = v___x_838_;
v___y_802_ = v___y_774_;
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
goto v___jp_800_;
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref_known(v___x_799_, 2);
lean_dec_ref(v_n_796_);
lean_dec_ref(v_semiringInst_794_);
lean_dec_ref(v_type_792_);
lean_del_object(v___x_789_);
v_a_839_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_833_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
v___jp_800_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_e_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_813_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3));
v___x_814_ = l_Lean_mkConst(v___x_813_, v___x_799_);
v_e_815_ = l_Lean_mkApp3(v___x_814_, v_type_792_, v_n_796_, v_ofNatInst_801_);
v___x_816_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_817_ = lean_int_dec_lt(v_k_773_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_e_815_);
v___x_819_ = v___x_789_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_e_815_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v___x_821_; 
lean_del_object(v___x_789_);
v___x_821_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_Expr_app___override(v_a_822_, v_e_815_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_dec_ref(v_e_815_);
return v___x_821_;
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_786_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_786_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_k_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v_k_856_);
return v_res_869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = l_Lean_Level_ofNat(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(lean_object* v_u_880_, lean_object* v_type_881_, lean_object* v_semiringInst_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0));
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
v___x_897_ = lean_box(0);
lean_inc(v_u_880_);
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v_u_880_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
lean_inc_ref(v___x_898_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v_u_880_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
lean_inc_ref(v___x_900_);
v___x_901_ = l_Lean_mkConst(v___x_895_, v___x_900_);
v___x_902_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_881_, 2);
v___x_903_ = l_Lean_mkApp3(v___x_901_, v_type_881_, v___x_902_, v_type_881_);
v___x_904_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_903_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_inst_x27_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_n(v_a_905_, 2);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3));
v___x_907_ = l_Lean_mkConst(v___x_906_, v___x_898_);
lean_inc_ref(v_type_881_);
v_inst_x27_908_ = l_Lean_mkAppB(v___x_907_, v_type_881_, v_semiringInst_882_);
v___x_909_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__5));
v___x_910_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_909_, v_a_905_, v_inst_x27_908_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = l_Lean_mkConst(v___x_909_, v___x_900_);
lean_inc_ref(v_type_881_);
v___x_912_ = l_Lean_mkApp4(v___x_911_, v_type_881_, v___x_902_, v_type_881_, v_a_905_);
v___x_913_ = l_Lean_Meta_Sym_canon(v___x_912_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Meta_Sym_shareCommon(v_a_914_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_915_;
}
else
{
return v___x_913_;
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_905_);
lean_dec_ref_known(v___x_900_, 2);
lean_dec_ref(v_type_881_);
v_a_916_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_910_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_910_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_900_, 2);
lean_dec_ref_known(v___x_898_, 2);
lean_dec_ref(v_semiringInst_882_);
lean_dec_ref(v_type_881_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(lean_object* v_u_924_, lean_object* v_type_925_, lean_object* v_semiringInst_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_924_, v_type_925_, v_semiringInst_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(lean_object* v_a_940_, lean_object* v_s_941_){
_start:
{
lean_object* v_toRing_942_; lean_object* v_invFn_x3f_943_; lean_object* v_divFn_x3f_944_; lean_object* v_zpowFn_x3f_945_; lean_object* v_semiringId_x3f_946_; lean_object* v_commSemiringInst_947_; lean_object* v_commRingInst_948_; lean_object* v_noZeroDivInst_x3f_949_; lean_object* v_fieldInst_x3f_950_; lean_object* v_powIdentityInst_x3f_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_983_; 
v_toRing_942_ = lean_ctor_get(v_s_941_, 0);
v_invFn_x3f_943_ = lean_ctor_get(v_s_941_, 1);
v_divFn_x3f_944_ = lean_ctor_get(v_s_941_, 2);
v_zpowFn_x3f_945_ = lean_ctor_get(v_s_941_, 3);
v_semiringId_x3f_946_ = lean_ctor_get(v_s_941_, 4);
v_commSemiringInst_947_ = lean_ctor_get(v_s_941_, 5);
v_commRingInst_948_ = lean_ctor_get(v_s_941_, 6);
v_noZeroDivInst_x3f_949_ = lean_ctor_get(v_s_941_, 7);
v_fieldInst_x3f_950_ = lean_ctor_get(v_s_941_, 8);
v_powIdentityInst_x3f_951_ = lean_ctor_get(v_s_941_, 9);
v_isSharedCheck_983_ = !lean_is_exclusive(v_s_941_);
if (v_isSharedCheck_983_ == 0)
{
v___x_953_ = v_s_941_;
v_isShared_954_ = v_isSharedCheck_983_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_powIdentityInst_x3f_951_);
lean_inc(v_fieldInst_x3f_950_);
lean_inc(v_noZeroDivInst_x3f_949_);
lean_inc(v_commRingInst_948_);
lean_inc(v_commSemiringInst_947_);
lean_inc(v_semiringId_x3f_946_);
lean_inc(v_zpowFn_x3f_945_);
lean_inc(v_divFn_x3f_944_);
lean_inc(v_invFn_x3f_943_);
lean_inc(v_toRing_942_);
lean_dec(v_s_941_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_983_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_id_955_; lean_object* v_type_956_; lean_object* v_u_957_; lean_object* v_ringInst_958_; lean_object* v_semiringInst_959_; lean_object* v_charInst_x3f_960_; uint8_t v_symbolicChar_961_; lean_object* v_addFn_x3f_962_; lean_object* v_mulFn_x3f_963_; lean_object* v_subFn_x3f_964_; lean_object* v_negFn_x3f_965_; lean_object* v_intCastFn_x3f_966_; lean_object* v_natCastFn_x3f_967_; lean_object* v_natSMulFn_x3f_968_; lean_object* v_intSMulFn_x3f_969_; lean_object* v_one_x3f_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_981_; 
v_id_955_ = lean_ctor_get(v_toRing_942_, 0);
v_type_956_ = lean_ctor_get(v_toRing_942_, 1);
v_u_957_ = lean_ctor_get(v_toRing_942_, 2);
v_ringInst_958_ = lean_ctor_get(v_toRing_942_, 3);
v_semiringInst_959_ = lean_ctor_get(v_toRing_942_, 4);
v_charInst_x3f_960_ = lean_ctor_get(v_toRing_942_, 5);
v_symbolicChar_961_ = lean_ctor_get_uint8(v_toRing_942_, sizeof(void*)*16);
v_addFn_x3f_962_ = lean_ctor_get(v_toRing_942_, 6);
v_mulFn_x3f_963_ = lean_ctor_get(v_toRing_942_, 7);
v_subFn_x3f_964_ = lean_ctor_get(v_toRing_942_, 8);
v_negFn_x3f_965_ = lean_ctor_get(v_toRing_942_, 9);
v_intCastFn_x3f_966_ = lean_ctor_get(v_toRing_942_, 11);
v_natCastFn_x3f_967_ = lean_ctor_get(v_toRing_942_, 12);
v_natSMulFn_x3f_968_ = lean_ctor_get(v_toRing_942_, 13);
v_intSMulFn_x3f_969_ = lean_ctor_get(v_toRing_942_, 14);
v_one_x3f_970_ = lean_ctor_get(v_toRing_942_, 15);
v_isSharedCheck_981_ = !lean_is_exclusive(v_toRing_942_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v_toRing_942_, 10);
lean_dec(v_unused_982_);
v___x_972_ = v_toRing_942_;
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_one_x3f_970_);
lean_inc(v_intSMulFn_x3f_969_);
lean_inc(v_natSMulFn_x3f_968_);
lean_inc(v_natCastFn_x3f_967_);
lean_inc(v_intCastFn_x3f_966_);
lean_inc(v_negFn_x3f_965_);
lean_inc(v_subFn_x3f_964_);
lean_inc(v_mulFn_x3f_963_);
lean_inc(v_addFn_x3f_962_);
lean_inc(v_charInst_x3f_960_);
lean_inc(v_semiringInst_959_);
lean_inc(v_ringInst_958_);
lean_inc(v_u_957_);
lean_inc(v_type_956_);
lean_inc(v_id_955_);
lean_dec(v_toRing_942_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_a_940_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 10, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_id_955_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_type_956_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_u_957_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_ringInst_958_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_semiringInst_959_);
lean_ctor_set(v_reuseFailAlloc_980_, 5, v_charInst_x3f_960_);
lean_ctor_set(v_reuseFailAlloc_980_, 6, v_addFn_x3f_962_);
lean_ctor_set(v_reuseFailAlloc_980_, 7, v_mulFn_x3f_963_);
lean_ctor_set(v_reuseFailAlloc_980_, 8, v_subFn_x3f_964_);
lean_ctor_set(v_reuseFailAlloc_980_, 9, v_negFn_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 10, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_980_, 11, v_intCastFn_x3f_966_);
lean_ctor_set(v_reuseFailAlloc_980_, 12, v_natCastFn_x3f_967_);
lean_ctor_set(v_reuseFailAlloc_980_, 13, v_natSMulFn_x3f_968_);
lean_ctor_set(v_reuseFailAlloc_980_, 14, v_intSMulFn_x3f_969_);
lean_ctor_set(v_reuseFailAlloc_980_, 15, v_one_x3f_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_980_, sizeof(void*)*16, v_symbolicChar_961_);
v___x_976_ = v_reuseFailAlloc_980_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_976_);
v___x_978_ = v___x_953_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_invFn_x3f_943_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_divFn_x3f_944_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_zpowFn_x3f_945_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_semiringId_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_979_, 5, v_commSemiringInst_947_);
lean_ctor_set(v_reuseFailAlloc_979_, 6, v_commRingInst_948_);
lean_ctor_set(v_reuseFailAlloc_979_, 7, v_noZeroDivInst_x3f_949_);
lean_ctor_set(v_reuseFailAlloc_979_, 8, v_fieldInst_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_979_, 9, v_powIdentityInst_x3f_951_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1030_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1030_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1030_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_toRing_1001_; lean_object* v_powFn_x3f_1002_; 
v_toRing_1001_ = lean_ctor_get(v_a_997_, 0);
lean_inc_ref(v_toRing_1001_);
lean_dec(v_a_997_);
v_powFn_x3f_1002_ = lean_ctor_get(v_toRing_1001_, 10);
if (lean_obj_tag(v_powFn_x3f_1002_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
lean_inc_ref(v_powFn_x3f_1002_);
lean_dec_ref(v_toRing_1001_);
v_val_1003_ = lean_ctor_get(v_powFn_x3f_1002_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v_powFn_x3f_1002_, 1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_val_1003_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_val_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v_type_1007_; lean_object* v_u_1008_; lean_object* v_semiringInst_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_999_);
v_type_1007_ = lean_ctor_get(v_toRing_1001_, 1);
lean_inc_ref(v_type_1007_);
v_u_1008_ = lean_ctor_get(v_toRing_1001_, 2);
lean_inc(v_u_1008_);
v_semiringInst_1009_ = lean_ctor_get(v_toRing_1001_, 4);
lean_inc_ref(v_semiringInst_1009_);
lean_dec_ref(v_toRing_1001_);
v___x_1010_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_1008_, v_type_1007_, v_semiringInst_1009_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc_n(v_a_1011_, 2);
lean_dec_ref_known(v___x_1010_, 1);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0), 2, 1);
lean_closure_set(v___f_1012_, 0, v_a_1011_);
v___x_1013_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1012_, v___y_984_, v___y_990_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_1013_, 0);
lean_dec(v_unused_1021_);
v___x_1015_ = v___x_1013_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_dec(v___x_1013_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_a_1011_);
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1011_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1011_);
v_a_1022_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1013_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1013_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_996_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_996_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(lean_object* v_pw_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_x_1065_; lean_object* v_k_1066_; lean_object* v___y_1068_; lean_object* v_a_1069_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_x_1065_ = lean_ctor_get(v_pw_1052_, 0);
lean_inc(v_x_1065_);
v_k_1066_ = lean_ctor_get(v_pw_1052_, 1);
lean_inc(v_k_1066_);
lean_dec_ref(v_pw_1052_);
v___x_1083_ = l_Lean_instInhabitedExpr;
v___x_1084_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_1053_, v___y_1054_, v___y_1062_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1101_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1101_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1101_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_toRingState_1089_; lean_object* v_vars_1090_; lean_object* v_size_1091_; uint8_t v___x_1092_; 
v_toRingState_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc_ref(v_toRingState_1089_);
lean_dec(v_a_1085_);
v_vars_1090_ = lean_ctor_get(v_toRingState_1089_, 0);
lean_inc_ref(v_vars_1090_);
lean_dec_ref(v_toRingState_1089_);
v_size_1091_ = lean_ctor_get(v_vars_1090_, 2);
v___x_1092_ = lean_nat_dec_lt(v_x_1065_, v_size_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec_ref(v_vars_1090_);
lean_dec(v_x_1065_);
v___x_1093_ = l_outOfBounds___redArg(v___x_1083_);
lean_inc(v___x_1093_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1093_);
v___x_1095_ = v___x_1087_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1068_ = v___x_1095_;
v_a_1069_ = v___x_1093_;
goto v___jp_1067_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1083_, v_vars_1090_, v_x_1065_);
lean_dec(v_x_1065_);
lean_dec_ref(v_vars_1090_);
lean_inc(v___x_1097_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1097_);
v___x_1099_ = v___x_1087_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
v___y_1068_ = v___x_1099_;
v_a_1069_ = v___x_1097_;
goto v___jp_1067_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_k_1066_);
lean_dec(v_x_1065_);
v_a_1102_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1084_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1084_);
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
v___jp_1067_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_dec_eq(v_k_1066_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v___y_1068_);
v___x_1072_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = l_Lean_mkNatLit(v_k_1066_);
v___x_1078_ = l_Lean_mkAppB(v_a_1073_, v_a_1069_, v___x_1077_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_dec_ref(v_a_1069_);
lean_dec(v_k_1066_);
return v___x_1072_;
}
}
else
{
lean_dec_ref(v_a_1069_);
lean_dec(v_k_1066_);
return v___y_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_pw_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_1124_, lean_object* v_s_1125_){
_start:
{
lean_object* v_toRing_1126_; lean_object* v_invFn_x3f_1127_; lean_object* v_divFn_x3f_1128_; lean_object* v_zpowFn_x3f_1129_; lean_object* v_semiringId_x3f_1130_; lean_object* v_commSemiringInst_1131_; lean_object* v_commRingInst_1132_; lean_object* v_noZeroDivInst_x3f_1133_; lean_object* v_fieldInst_x3f_1134_; lean_object* v_powIdentityInst_x3f_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1167_; 
v_toRing_1126_ = lean_ctor_get(v_s_1125_, 0);
v_invFn_x3f_1127_ = lean_ctor_get(v_s_1125_, 1);
v_divFn_x3f_1128_ = lean_ctor_get(v_s_1125_, 2);
v_zpowFn_x3f_1129_ = lean_ctor_get(v_s_1125_, 3);
v_semiringId_x3f_1130_ = lean_ctor_get(v_s_1125_, 4);
v_commSemiringInst_1131_ = lean_ctor_get(v_s_1125_, 5);
v_commRingInst_1132_ = lean_ctor_get(v_s_1125_, 6);
v_noZeroDivInst_x3f_1133_ = lean_ctor_get(v_s_1125_, 7);
v_fieldInst_x3f_1134_ = lean_ctor_get(v_s_1125_, 8);
v_powIdentityInst_x3f_1135_ = lean_ctor_get(v_s_1125_, 9);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_s_1125_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1137_ = v_s_1125_;
v_isShared_1138_ = v_isSharedCheck_1167_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1135_);
lean_inc(v_fieldInst_x3f_1134_);
lean_inc(v_noZeroDivInst_x3f_1133_);
lean_inc(v_commRingInst_1132_);
lean_inc(v_commSemiringInst_1131_);
lean_inc(v_semiringId_x3f_1130_);
lean_inc(v_zpowFn_x3f_1129_);
lean_inc(v_divFn_x3f_1128_);
lean_inc(v_invFn_x3f_1127_);
lean_inc(v_toRing_1126_);
lean_dec(v_s_1125_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1167_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_id_1139_; lean_object* v_type_1140_; lean_object* v_u_1141_; lean_object* v_ringInst_1142_; lean_object* v_semiringInst_1143_; lean_object* v_charInst_x3f_1144_; uint8_t v_symbolicChar_1145_; lean_object* v_addFn_x3f_1146_; lean_object* v_subFn_x3f_1147_; lean_object* v_negFn_x3f_1148_; lean_object* v_powFn_x3f_1149_; lean_object* v_intCastFn_x3f_1150_; lean_object* v_natCastFn_x3f_1151_; lean_object* v_natSMulFn_x3f_1152_; lean_object* v_intSMulFn_x3f_1153_; lean_object* v_one_x3f_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1165_; 
v_id_1139_ = lean_ctor_get(v_toRing_1126_, 0);
v_type_1140_ = lean_ctor_get(v_toRing_1126_, 1);
v_u_1141_ = lean_ctor_get(v_toRing_1126_, 2);
v_ringInst_1142_ = lean_ctor_get(v_toRing_1126_, 3);
v_semiringInst_1143_ = lean_ctor_get(v_toRing_1126_, 4);
v_charInst_x3f_1144_ = lean_ctor_get(v_toRing_1126_, 5);
v_symbolicChar_1145_ = lean_ctor_get_uint8(v_toRing_1126_, sizeof(void*)*16);
v_addFn_x3f_1146_ = lean_ctor_get(v_toRing_1126_, 6);
v_subFn_x3f_1147_ = lean_ctor_get(v_toRing_1126_, 8);
v_negFn_x3f_1148_ = lean_ctor_get(v_toRing_1126_, 9);
v_powFn_x3f_1149_ = lean_ctor_get(v_toRing_1126_, 10);
v_intCastFn_x3f_1150_ = lean_ctor_get(v_toRing_1126_, 11);
v_natCastFn_x3f_1151_ = lean_ctor_get(v_toRing_1126_, 12);
v_natSMulFn_x3f_1152_ = lean_ctor_get(v_toRing_1126_, 13);
v_intSMulFn_x3f_1153_ = lean_ctor_get(v_toRing_1126_, 14);
v_one_x3f_1154_ = lean_ctor_get(v_toRing_1126_, 15);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_toRing_1126_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_toRing_1126_, 7);
lean_dec(v_unused_1166_);
v___x_1156_ = v_toRing_1126_;
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_one_x3f_1154_);
lean_inc(v_intSMulFn_x3f_1153_);
lean_inc(v_natSMulFn_x3f_1152_);
lean_inc(v_natCastFn_x3f_1151_);
lean_inc(v_intCastFn_x3f_1150_);
lean_inc(v_powFn_x3f_1149_);
lean_inc(v_negFn_x3f_1148_);
lean_inc(v_subFn_x3f_1147_);
lean_inc(v_addFn_x3f_1146_);
lean_inc(v_charInst_x3f_1144_);
lean_inc(v_semiringInst_1143_);
lean_inc(v_ringInst_1142_);
lean_inc(v_u_1141_);
lean_inc(v_type_1140_);
lean_inc(v_id_1139_);
lean_dec(v_toRing_1126_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_a_1124_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 7, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_id_1139_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_type_1140_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_u_1141_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_ringInst_1142_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_semiringInst_1143_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_charInst_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_addFn_x3f_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1164_, 8, v_subFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 9, v_negFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 10, v_powFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 11, v_intCastFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 12, v_natCastFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 13, v_natSMulFn_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 14, v_intSMulFn_x3f_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 15, v_one_x3f_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*16, v_symbolicChar_1145_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1160_);
v___x_1162_ = v___x_1137_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_invFn_x3f_1127_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_divFn_x3f_1128_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_zpowFn_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_semiringId_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1163_, 5, v_commSemiringInst_1131_);
lean_ctor_set(v_reuseFailAlloc_1163_, 6, v_commRingInst_1132_);
lean_ctor_set(v_reuseFailAlloc_1163_, 7, v_noZeroDivInst_x3f_1133_);
lean_ctor_set(v_reuseFailAlloc_1163_, 8, v_fieldInst_x3f_1134_);
lean_ctor_set(v_reuseFailAlloc_1163_, 9, v_powIdentityInst_x3f_1135_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1235_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1235_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1235_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_toRing_1196_; lean_object* v_mulFn_x3f_1197_; 
v_toRing_1196_ = lean_ctor_get(v_a_1192_, 0);
lean_inc_ref(v_toRing_1196_);
lean_dec(v_a_1192_);
v_mulFn_x3f_1197_ = lean_ctor_get(v_toRing_1196_, 7);
if (lean_obj_tag(v_mulFn_x3f_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1200_; 
lean_inc_ref(v_mulFn_x3f_1197_);
lean_dec_ref(v_toRing_1196_);
v_val_1198_ = lean_ctor_get(v_mulFn_x3f_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_mulFn_x3f_1197_, 1);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_val_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_val_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
else
{
lean_object* v_type_1202_; lean_object* v_u_1203_; lean_object* v_semiringInst_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_expectedInst_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_del_object(v___x_1194_);
v_type_1202_ = lean_ctor_get(v_toRing_1196_, 1);
lean_inc_ref_n(v_type_1202_, 3);
v_u_1203_ = lean_ctor_get(v_toRing_1196_, 2);
lean_inc_n(v_u_1203_, 2);
v_semiringInst_1204_ = lean_ctor_get(v_toRing_1196_, 4);
lean_inc_ref(v_semiringInst_1204_);
lean_dec_ref(v_toRing_1196_);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1));
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_u_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
lean_inc_ref(v___x_1207_);
v___x_1208_ = l_Lean_mkConst(v___x_1205_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3));
v___x_1210_ = l_Lean_mkConst(v___x_1209_, v___x_1207_);
v___x_1211_ = l_Lean_mkAppB(v___x_1210_, v_type_1202_, v_semiringInst_1204_);
v_expectedInst_1212_ = l_Lean_mkAppB(v___x_1208_, v_type_1202_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4));
v___x_1214_ = ((lean_object*)(l_Int_Internal_Linear_Poly_isNonlinear___redArg___closed__2));
v___x_1215_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_1202_, v_u_1203_, v___x_1213_, v___x_1214_, v_expectedInst_1212_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_n(v_a_1216_, 2);
lean_dec_ref_known(v___x_1215_, 1);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1217_, 0, v_a_1216_);
v___x_1218_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1217_, v___y_1179_, v___y_1185_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1226_);
v___x_1220_ = v___x_1218_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1218_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_a_1216_);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1216_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_a_1216_);
v_a_1227_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1218_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1218_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1191_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1191_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(lean_object* v_mn_1257_, lean_object* v_acc_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
if (lean_obj_tag(v_mn_1257_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_acc_1258_);
return v___x_1271_;
}
else
{
lean_object* v_p_1272_; lean_object* v_m_1273_; lean_object* v___x_1274_; 
v_p_1272_ = lean_ctor_get(v_mn_1257_, 0);
lean_inc_ref(v_p_1272_);
v_m_1273_ = lean_ctor_get(v_mn_1257_, 1);
lean_inc(v_m_1273_);
lean_dec_ref_known(v_mn_1257_, 2);
v___x_1274_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1272_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_Lean_mkAppB(v_a_1275_, v_acc_1258_, v_a_1277_);
v_mn_1257_ = v_m_1273_;
v_acc_1258_ = v___x_1278_;
goto _start;
}
else
{
lean_dec(v_a_1275_);
lean_dec(v_m_1273_);
lean_dec_ref(v_acc_1258_);
return v___x_1276_;
}
}
else
{
lean_dec(v_m_1273_);
lean_dec_ref(v_p_1272_);
lean_dec_ref(v_acc_1258_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_mn_1280_, lean_object* v_acc_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_mn_1280_, v_acc_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_to_int(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(lean_object* v_mn_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
if (lean_obj_tag(v_mn_1297_) == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1311_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_1310_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1311_;
}
else
{
lean_object* v_p_1312_; lean_object* v_m_1313_; lean_object* v___x_1314_; 
v_p_1312_ = lean_ctor_get(v_mn_1297_, 0);
lean_inc_ref(v_p_1312_);
v_m_1313_ = lean_ctor_get(v_mn_1297_, 1);
lean_inc(v_m_1313_);
lean_dec_ref_known(v_mn_1297_, 2);
v___x_1314_ = l_Lean_Meta_Sym_Arith_denotePower___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_1312_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denoteMon_go___at___00Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_1313_, v_a_1315_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1316_;
}
else
{
lean_dec(v_m_1313_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mn_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(lean_object* v_k_1331_, lean_object* v_mn_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0, &l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once, _init_l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
v___x_1346_ = lean_int_dec_eq(v_k_1331_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_Lean_mkAppB(v_a_1348_, v_a_1350_, v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_dec(v_a_1350_);
lean_dec(v_a_1348_);
return v___x_1351_;
}
}
else
{
lean_dec(v_a_1348_);
lean_dec(v_mn_1332_);
return v___x_1349_;
}
}
else
{
lean_dec(v_mn_1332_);
return v___x_1347_;
}
}
else
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_Sym_Arith_denoteMon___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_mn_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(lean_object* v_k_1362_, lean_object* v_mn_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1362_, v_mn_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v_k_1362_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(lean_object* v_p_1377_, lean_object* v_acc_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
if (lean_obj_tag(v_p_1377_) == 0)
{
lean_object* v_k_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1412_; 
v_k_1391_ = lean_ctor_get(v_p_1377_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_p_1377_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1393_ = v_p_1377_;
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_k_1391_);
lean_dec(v_p_1377_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
v___x_1396_ = lean_int_dec_eq(v_k_1391_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_del_object(v___x_1393_);
v___x_1397_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1391_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v_k_1391_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = l_Lean_mkAppB(v_a_1398_, v_acc_1378_, v_a_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_dec(v_a_1398_);
lean_dec_ref(v_acc_1378_);
return v___x_1399_;
}
}
else
{
lean_dec(v_k_1391_);
lean_dec_ref(v_acc_1378_);
return v___x_1397_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_k_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_acc_1378_);
v___x_1410_ = v___x_1393_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_acc_1378_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_k_1413_; lean_object* v_v_1414_; lean_object* v_p_1415_; lean_object* v___x_1416_; 
v_k_1413_ = lean_ctor_get(v_p_1377_, 0);
lean_inc(v_k_1413_);
v_v_1414_ = lean_ctor_get(v_p_1377_, 1);
lean_inc(v_v_1414_);
v_p_1415_ = lean_ctor_get(v_p_1377_, 2);
lean_inc_ref(v_p_1415_);
lean_dec_ref_known(v_p_1377_, 3);
v___x_1416_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1413_, v_v_1414_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v_k_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_mkAppB(v_a_1417_, v_acc_1378_, v_a_1419_);
v_p_1377_ = v_p_1415_;
v_acc_1378_ = v___x_1420_;
goto _start;
}
else
{
lean_dec(v_a_1417_);
lean_dec_ref(v_p_1415_);
lean_dec_ref(v_acc_1378_);
return v___x_1418_;
}
}
else
{
lean_dec_ref(v_p_1415_);
lean_dec(v_v_1414_);
lean_dec(v_k_1413_);
lean_dec_ref(v_acc_1378_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(lean_object* v_p_1422_, lean_object* v_acc_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1422_, v_acc_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(lean_object* v_p_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
if (lean_obj_tag(v_p_1437_) == 0)
{
lean_object* v_k_1450_; lean_object* v___x_1451_; 
v_k_1450_ = lean_ctor_get(v_p_1437_, 0);
lean_inc(v_k_1450_);
lean_dec_ref_known(v_p_1437_, 1);
v___x_1451_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_1450_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v_k_1450_);
return v___x_1451_;
}
else
{
lean_object* v_k_1452_; lean_object* v_v_1453_; lean_object* v_p_1454_; lean_object* v___x_1455_; 
v_k_1452_ = lean_ctor_get(v_p_1437_, 0);
lean_inc(v_k_1452_);
v_v_1453_ = lean_ctor_get(v_p_1437_, 1);
lean_inc(v_v_1453_);
v_p_1454_ = lean_ctor_get(v_p_1437_, 2);
lean_inc_ref(v_p_1454_);
lean_dec_ref_known(v_p_1437_, 3);
v___x_1455_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_denoteTerm___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_1452_, v_v_1453_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v_k_1452_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = l___private_Lean_Meta_Sym_Arith_DenoteExpr_0__Lean_Meta_Sym_Arith_denotePoly_go___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_1454_, v_a_1456_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1457_;
}
else
{
lean_dec_ref(v_p_1454_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0___boxed(lean_object* v_p_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_p_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1471_;
}
}
static double _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1472_; double v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_float_of_nat(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(lean_object* v_cls_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1531_; 
v_ref_1484_ = lean_ctor_get(v___y_1481_, 2);
v___x_1485_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1531_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1531_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v_traceState_1491_; lean_object* v_env_1492_; lean_object* v_nextMacroScope_1493_; lean_object* v_ngen_1494_; lean_object* v_auxDeclNGen_1495_; lean_object* v_cache_1496_; lean_object* v_recordedDeps_1497_; lean_object* v_messages_1498_; lean_object* v_infoState_1499_; lean_object* v_snapshotTasks_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1530_; 
v___x_1490_ = lean_st_ref_take(v___y_1482_);
v_traceState_1491_ = lean_ctor_get(v___x_1490_, 4);
v_env_1492_ = lean_ctor_get(v___x_1490_, 0);
v_nextMacroScope_1493_ = lean_ctor_get(v___x_1490_, 1);
v_ngen_1494_ = lean_ctor_get(v___x_1490_, 2);
v_auxDeclNGen_1495_ = lean_ctor_get(v___x_1490_, 3);
v_cache_1496_ = lean_ctor_get(v___x_1490_, 5);
v_recordedDeps_1497_ = lean_ctor_get(v___x_1490_, 6);
v_messages_1498_ = lean_ctor_get(v___x_1490_, 7);
v_infoState_1499_ = lean_ctor_get(v___x_1490_, 8);
v_snapshotTasks_1500_ = lean_ctor_get(v___x_1490_, 9);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1502_ = v___x_1490_;
v_isShared_1503_ = v_isSharedCheck_1530_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snapshotTasks_1500_);
lean_inc(v_infoState_1499_);
lean_inc(v_messages_1498_);
lean_inc(v_recordedDeps_1497_);
lean_inc(v_cache_1496_);
lean_inc(v_traceState_1491_);
lean_inc(v_auxDeclNGen_1495_);
lean_inc(v_ngen_1494_);
lean_inc(v_nextMacroScope_1493_);
lean_inc(v_env_1492_);
lean_dec(v___x_1490_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1530_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
uint64_t v_tid_1504_; lean_object* v_traces_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1529_; 
v_tid_1504_ = lean_ctor_get_uint64(v_traceState_1491_, sizeof(void*)*1);
v_traces_1505_ = lean_ctor_get(v_traceState_1491_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_traceState_1491_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1507_ = v_traceState_1491_;
v_isShared_1508_ = v_isSharedCheck_1529_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_traces_1505_);
lean_dec(v_traceState_1491_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1529_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; double v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_float_once(&l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
v___x_1512_ = 0;
v___x_1513_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1));
v___x_1514_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1514_, 0, v_cls_1477_);
lean_ctor_set(v___x_1514_, 1, v___x_1510_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
lean_ctor_set_float(v___x_1514_, sizeof(void*)*3, v___x_1511_);
lean_ctor_set_float(v___x_1514_, sizeof(void*)*3 + 8, v___x_1511_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*3 + 16, v___x_1512_);
v___x_1515_ = ((lean_object*)(l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2));
v___x_1516_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v_a_1486_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
lean_inc(v_ref_1484_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_ref_1484_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = l_Lean_PersistentArray_push___redArg(v_traces_1505_, v___x_1517_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1518_);
v___x_1520_ = v___x_1507_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1518_);
lean_ctor_set_uint64(v_reuseFailAlloc_1528_, sizeof(void*)*1, v_tid_1504_);
v___x_1520_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v___x_1520_);
v___x_1522_ = v___x_1502_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_env_1492_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_nextMacroScope_1493_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_ngen_1494_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_auxDeclNGen_1495_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1527_, 5, v_cache_1496_);
lean_ctor_set(v_reuseFailAlloc_1527_, 6, v_recordedDeps_1497_);
lean_ctor_set(v_reuseFailAlloc_1527_, 7, v_messages_1498_);
lean_ctor_set(v_reuseFailAlloc_1527_, 8, v_infoState_1499_);
lean_ctor_set(v_reuseFailAlloc_1527_, 9, v_snapshotTasks_1500_);
v___x_1522_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_st_ref_put(v___y_1482_, v___x_1522_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1509_);
v___x_1525_ = v___x_1488_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1509_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(lean_object* v_cls_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1539_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1555_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__7));
v___x_1556_ = l_Lean_Name_append(v___x_1555_, v___x_1554_);
return v___x_1556_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__9));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object* v_p_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Int_Internal_Linear_Poly_isNonlinear___redArg(v_p_1560_, v_a_1561_, v_a_1569_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1799_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1799_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1799_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_unbox(v_a_1573_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v___x_1578_ = lean_box(0);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v___f_1582_; lean_object* v___x_1583_; 
lean_del_object(v___x_1575_);
lean_inc(v_a_1573_);
v___f_1582_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1582_, 0, v_a_1573_);
v___x_1583_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___redArg(v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1790_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1790_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1790_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
if (lean_obj_tag(v_a_1584_) == 1)
{
lean_object* v_val_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_del_object(v___x_1586_);
v_val_1588_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1589_ = 0;
v___x_1590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1590_, 0, v_val_1588_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*1, v___x_1589_);
lean_inc_ref(v_p_1560_);
v___x_1591_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1560_, v_a_1561_, v_a_1569_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = l_Lean_Meta_Sym_canon(v_a_1592_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = l_Lean_Meta_Sym_shareCommon(v_a_1594_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
lean_inc_ref(v_p_1560_);
v___x_1597_ = l_Int_Internal_Linear_Poly_getGeneration___redArg(v_p_1560_, v_a_1561_, v_a_1569_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1599_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
v___x_1600_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_a_1596_, v___x_1599_, v___x_1590_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1745_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1745_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1745_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
if (lean_obj_tag(v_a_1601_) == 1)
{
lean_object* v_val_1605_; lean_object* v___x_1606_; 
lean_del_object(v___x_1603_);
v_val_1605_ = lean_ctor_get(v_a_1601_, 0);
lean_inc_n(v_val_1605_, 2);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1606_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(v_val_1605_, v___x_1590_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1732_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1732_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1732_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
if (lean_obj_tag(v_a_1607_) == 1)
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1727_; 
lean_del_object(v___x_1609_);
v_val_1611_ = lean_ctor_get(v_a_1607_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1613_ = v_a_1607_;
v_isShared_1614_ = v_isSharedCheck_1727_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v_a_1607_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1727_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; 
lean_inc(v_val_1611_);
v___x_1615_ = l_Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0(v_val_1611_, v___x_1590_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
lean_dec_ref_known(v___x_1590_, 1);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1616_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_n(v_a_1618_, 2);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__0);
lean_inc(v_a_1570_);
lean_inc_ref(v_a_1569_);
lean_inc(v_a_1568_);
lean_inc_ref(v_a_1567_);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc(v_a_1561_);
v___x_1620_ = lean_grind_internalize(v_a_1618_, v_a_1598_, v___x_1619_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1701_; 
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1702_);
v___x_1622_ = v___x_1620_;
v_isShared_1623_ = v_isSharedCheck_1701_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v___x_1620_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1701_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_a_1618_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1692_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1692_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1692_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1560_, v_a_1625_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_del_object(v___x_1622_);
v___x_1639_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1640_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1639_, v___f_1582_, v_a_1561_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_toCold_1641_; lean_object* v_options_1642_; uint8_t v_hasTrace_1643_; 
lean_dec_ref_known(v___x_1640_, 1);
v_toCold_1641_ = lean_ctor_get(v_a_1569_, 0);
v_options_1642_ = lean_ctor_get(v_toCold_1641_, 2);
v_hasTrace_1643_ = lean_ctor_get_uint8(v_options_1642_, sizeof(void*)*1);
if (v_hasTrace_1643_ == 0)
{
lean_dec_ref(v_p_1560_);
goto v___jp_1629_;
}
else
{
lean_object* v_inheritedTraceOptions_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_inheritedTraceOptions_1644_ = lean_ctor_get(v_toCold_1641_, 11);
v___x_1645_ = ((lean_object*)(l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__5));
v___x_1646_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__8);
v___x_1647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1644_, v_options_1642_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_dec_ref(v_p_1560_);
goto v___jp_1629_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1560_, v_a_1561_, v_a_1569_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
lean_inc(v_a_1625_);
v___x_1650_ = l_Int_Internal_Linear_Poly_pp___redArg(v_a_1625_, v_a_1561_, v_a_1569_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_obj_once(&l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10, &l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10_once, _init_l_Int_Internal_Linear_Poly_normCommRing_x3f___closed__10);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_a_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_a_1651_);
v___x_1655_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_1645_, v___x_1654_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_dec_ref_known(v___x_1655_, 1);
goto v___jp_1629_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1627_);
lean_dec(v_a_1625_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1649_);
lean_del_object(v___x_1627_);
lean_dec(v_a_1625_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
v_a_1664_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1650_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1650_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_del_object(v___x_1627_);
lean_dec(v_a_1625_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
v_a_1672_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1648_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1648_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_del_object(v___x_1627_);
lean_dec(v_a_1625_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec_ref(v_p_1560_);
v_a_1680_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1640_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1640_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_del_object(v___x_1627_);
lean_dec(v_a_1625_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v___x_1688_ = lean_box(0);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1688_);
v___x_1690_ = v___x_1622_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
v___jp_1629_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_val_1611_);
lean_ctor_set(v___x_1630_, 1, v_a_1625_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_val_1605_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1631_);
v___x_1633_ = v___x_1613_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1633_);
v___x_1635_ = v___x_1627_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1622_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1693_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1624_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1624_);
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
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1618_);
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1703_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1620_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1620_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec(v_a_1598_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1711_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1617_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1617_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_del_object(v___x_1613_);
lean_dec(v_val_1611_);
lean_dec(v_val_1605_);
lean_dec(v_a_1598_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1719_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1615_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1615_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec(v_a_1607_);
lean_dec(v_val_1605_);
lean_dec(v_a_1598_);
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v___x_1728_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1728_);
v___x_1730_ = v___x_1609_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
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
lean_dec(v_val_1605_);
lean_dec(v_a_1598_);
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1733_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1606_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1606_);
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
else
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_dec(v_a_1601_);
lean_dec(v_a_1598_);
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v___x_1741_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1741_);
v___x_1743_ = v___x_1603_;
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
lean_dec(v_a_1598_);
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_p_1560_);
v_a_1746_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1600_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1600_);
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
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1596_);
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v_a_1754_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1597_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1597_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v_a_1762_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1595_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1595_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v_a_1770_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1593_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1593_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref_known(v___x_1590_, 1);
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v_a_1778_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1591_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1591_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_a_1584_);
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v___x_1786_ = lean_box(0);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1786_);
v___x_1788_ = v___x_1586_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
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
lean_dec_ref(v___f_1582_);
lean_dec(v_a_1573_);
lean_dec_ref(v_p_1560_);
v_a_1791_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1583_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1583_);
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
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_p_1560_);
v_a_1800_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1572_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1572_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f___boxed(lean_object* v_p_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec(v_a_1809_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(lean_object* v_cls_1821_, lean_object* v_msg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___redArg(v_cls_1821_, v_msg_1822_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1___boxed(lean_object* v_cls_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_addTrace___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__1(v_cls_1836_, v_msg_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(lean_object* v_00_u03b1_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_1852_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00Lean_Meta_Sym_Arith_denotePoly___at___00Int_Internal_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_1866_, v_msg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1880_;
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
