// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing import Lean.Meta.NatInstTesters public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Data.Nat.Dvd
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_bmodCoeffs(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_norm(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 149, 0, 200, 120, 117, 225, 20)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(4, 93, 162, 5, 159, 42, 23, 43)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "non-linear divisibility constraint found"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "emod_pos_of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(38, 146, 134, 59, 191, 125, 100, 172)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "of_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 103, 37, 221, 182, 135, 125, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(lean_object* v_c_5_){
_start:
{
lean_object* v_d_6_; lean_object* v_p_7_; lean_object* v_d_8_; lean_object* v___y_10_; lean_object* v___y_11_; lean_object* v___x_17_; lean_object* v___y_19_; uint8_t v___x_23_; 
v_d_6_ = lean_ctor_get(v_c_5_, 0);
v_p_7_ = lean_ctor_get(v_c_5_, 1);
v_d_8_ = lean_nat_abs(v_d_6_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_dec_le(v_d_8_, v___x_17_);
if (v___x_23_ == 0)
{
if (lean_obj_tag(v_p_7_) == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___y_19_ = v___x_24_;
goto v___jp_18_;
}
else
{
lean_object* v_k_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_k_25_ = lean_ctor_get(v_p_7_, 0);
v___x_26_ = lean_nat_abs(v_k_25_);
v___x_27_ = lean_nat_dec_eq(v___x_26_, v___x_17_);
lean_dec(v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_snd_30_; lean_object* v_fst_31_; lean_object* v_fst_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
lean_inc(v_d_8_);
v___x_28_ = lean_nat_to_int(v_d_8_);
v___x_29_ = l_Lean_Meta_Grind_Arith_gcdExt(v_k_25_, v___x_28_);
lean_dec(v___x_28_);
v_snd_30_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_snd_30_);
v_fst_31_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_fst_31_);
lean_dec_ref(v___x_29_);
v_fst_32_ = lean_ctor_get(v_snd_30_, 0);
lean_inc(v_fst_32_);
lean_dec(v_snd_30_);
v___x_33_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_34_ = lean_int_dec_eq(v_fst_31_, v___x_33_);
lean_dec(v_fst_31_);
if (v___x_34_ == 0)
{
lean_dec(v_fst_32_);
v___y_19_ = v___x_33_;
goto v___jp_18_;
}
else
{
v___y_19_ = v_fst_32_;
goto v___jp_18_;
}
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___y_19_ = v___x_35_;
goto v___jp_18_;
}
}
}
else
{
lean_dec(v_d_8_);
return v_c_5_;
}
v___jp_9_:
{
lean_object* v_p_12_; uint8_t v___x_13_; 
v_p_12_ = l_Int_Internal_Linear_Poly_bmodCoeffs(v_d_8_, v___y_11_);
v___x_13_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_12_, v_p_7_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc(v_d_6_);
v___x_14_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_14_, 0, v_c_5_);
lean_ctor_set(v___x_14_, 1, v___y_10_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_d_6_);
lean_ctor_set(v___x_16_, 1, v_p_12_);
lean_ctor_set(v___x_16_, 2, v___x_14_);
lean_ctor_set(v___x_16_, 3, v___x_15_);
return v___x_16_;
}
else
{
lean_dec_ref(v_p_12_);
lean_dec(v___y_10_);
return v_c_5_;
}
}
v___jp_18_:
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_21_ = lean_int_dec_eq(v___y_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_inc_ref(v_p_7_);
v___x_22_ = l_Int_Internal_Linear_Poly_mul(v_p_7_, v___y_19_);
v___y_10_ = v___y_19_;
v___y_11_ = v___x_22_;
goto v___jp_9_;
}
else
{
lean_inc_ref(v_p_7_);
v___y_10_ = v___y_19_;
v___y_11_ = v_p_7_;
goto v___jp_9_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* v_c_38_){
_start:
{
lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_44_; lean_object* v___y_59_; lean_object* v_d_60_; lean_object* v_p_61_; lean_object* v_d_66_; lean_object* v_p_67_; uint8_t v___x_68_; 
v_d_66_ = lean_ctor_get(v_c_38_, 0);
lean_inc(v_d_66_);
v_p_67_ = lean_ctor_get(v_c_38_, 1);
v___x_68_ = l_Int_Internal_Linear_Poly_isSorted(v_p_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_inc_ref(v_p_67_);
v___x_69_ = l_Int_Internal_Linear_Poly_norm(v_p_67_);
v___x_70_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_70_, 0, v_c_38_);
v___x_71_ = lean_box(0);
lean_inc_ref(v___x_69_);
lean_inc(v_d_66_);
v___x_72_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_72_, 0, v_d_66_);
lean_ctor_set(v___x_72_, 1, v___x_69_);
lean_ctor_set(v___x_72_, 2, v___x_70_);
lean_ctor_set(v___x_72_, 3, v___x_71_);
v___y_59_ = v___x_72_;
v_d_60_ = v_d_66_;
v_p_61_ = v___x_69_;
goto v___jp_58_;
}
else
{
lean_inc_ref(v_p_67_);
v___y_59_ = v_c_38_;
v_d_60_ = v_d_66_;
v_p_61_ = v_p_67_;
goto v___jp_58_;
}
v___jp_39_:
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_45_ = l_Int_Internal_Linear_Poly_getConst(v___y_40_);
v___x_46_ = lean_int_emod(v___x_45_, v___y_44_);
lean_dec(v___x_45_);
v___x_47_ = lean_int_dec_eq(v___x_46_, v___y_42_);
lean_dec(v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec(v___y_44_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
v___x_48_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_43_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_50_ = lean_int_dec_eq(v___y_44_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_51_ = lean_int_ediv(v___y_41_, v___y_44_);
lean_dec(v___y_41_);
v___x_52_ = l_Int_Internal_Linear_Poly_div(v___y_44_, v___y_40_);
lean_dec(v___y_44_);
v___x_53_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_53_, 0, v___y_43_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_55_, 0, v___x_51_);
lean_ctor_set(v___x_55_, 1, v___x_52_);
lean_ctor_set(v___x_55_, 2, v___x_53_);
lean_ctor_set(v___x_55_, 3, v___x_54_);
v___x_56_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___x_55_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
lean_dec(v___y_44_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
v___x_57_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_43_);
return v___x_57_;
}
}
}
v___jp_58_:
{
lean_object* v_g_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
lean_inc(v_d_60_);
v_g_62_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_61_, v_d_60_);
v___x_63_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_64_ = lean_int_dec_lt(v_d_60_, v___x_63_);
if (v___x_64_ == 0)
{
v___y_40_ = v_p_61_;
v___y_41_ = v_d_60_;
v___y_42_ = v___x_63_;
v___y_43_ = v___y_59_;
v___y_44_ = v_g_62_;
goto v___jp_39_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_int_neg(v_g_62_);
lean_dec(v_g_62_);
v___y_40_ = v_p_61_;
v___y_41_ = v_d_60_;
v___y_42_ = v___x_63_;
v___y_43_ = v___y_59_;
v___y_44_ = v___x_65_;
goto v___jp_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; lean_object* v_env_80_; uint8_t v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_79_ = lean_st_ref_get(v___y_77_);
v_env_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_env_80_);
lean_dec(v___x_79_);
v___x_81_ = 0;
v_env_82_ = l_Lean_Environment_setRecordingDeps(v_env_80_, v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_75_);
v_toCold_84_ = lean_ctor_get(v___y_76_, 0);
v_mctx_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_83_);
v_lctx_86_ = lean_ctor_get(v___y_74_, 2);
v_options_87_ = lean_ctor_get(v_toCold_84_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_82_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_73_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_98_; double v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_float_of_nat(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_103_, lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_157_; 
v_ref_110_ = lean_ctor_get(v___y_107_, 2);
v___x_111_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_157_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_157_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_157_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v_traceState_117_; lean_object* v_env_118_; lean_object* v_nextMacroScope_119_; lean_object* v_ngen_120_; lean_object* v_auxDeclNGen_121_; lean_object* v_cache_122_; lean_object* v_recordedDeps_123_; lean_object* v_messages_124_; lean_object* v_infoState_125_; lean_object* v_snapshotTasks_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_156_; 
v___x_116_ = lean_st_ref_take(v___y_108_);
v_traceState_117_ = lean_ctor_get(v___x_116_, 4);
v_env_118_ = lean_ctor_get(v___x_116_, 0);
v_nextMacroScope_119_ = lean_ctor_get(v___x_116_, 1);
v_ngen_120_ = lean_ctor_get(v___x_116_, 2);
v_auxDeclNGen_121_ = lean_ctor_get(v___x_116_, 3);
v_cache_122_ = lean_ctor_get(v___x_116_, 5);
v_recordedDeps_123_ = lean_ctor_get(v___x_116_, 6);
v_messages_124_ = lean_ctor_get(v___x_116_, 7);
v_infoState_125_ = lean_ctor_get(v___x_116_, 8);
v_snapshotTasks_126_ = lean_ctor_get(v___x_116_, 9);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_156_ == 0)
{
v___x_128_ = v___x_116_;
v_isShared_129_ = v_isSharedCheck_156_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_snapshotTasks_126_);
lean_inc(v_infoState_125_);
lean_inc(v_messages_124_);
lean_inc(v_recordedDeps_123_);
lean_inc(v_cache_122_);
lean_inc(v_traceState_117_);
lean_inc(v_auxDeclNGen_121_);
lean_inc(v_ngen_120_);
lean_inc(v_nextMacroScope_119_);
lean_inc(v_env_118_);
lean_dec(v___x_116_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_156_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
uint64_t v_tid_130_; lean_object* v_traces_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_155_; 
v_tid_130_ = lean_ctor_get_uint64(v_traceState_117_, sizeof(void*)*1);
v_traces_131_ = lean_ctor_get(v_traceState_117_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_traceState_117_);
if (v_isSharedCheck_155_ == 0)
{
v___x_133_ = v_traceState_117_;
v_isShared_134_ = v_isSharedCheck_155_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_traces_131_);
lean_dec(v_traceState_117_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_155_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; double v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_box(0);
v___x_137_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_138_ = 0;
v___x_139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_140_, 0, v_cls_103_);
lean_ctor_set(v___x_140_, 1, v___x_136_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
lean_ctor_set_float(v___x_140_, sizeof(void*)*3, v___x_137_);
lean_ctor_set_float(v___x_140_, sizeof(void*)*3 + 8, v___x_137_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*3 + 16, v___x_138_);
v___x_141_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_142_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v_a_112_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
lean_inc(v_ref_110_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v_ref_110_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = l_Lean_PersistentArray_push___redArg(v_traces_131_, v___x_143_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_144_);
v___x_146_ = v___x_133_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_144_);
lean_ctor_set_uint64(v_reuseFailAlloc_154_, sizeof(void*)*1, v_tid_130_);
v___x_146_ = v_reuseFailAlloc_154_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 4, v___x_146_);
v___x_148_ = v___x_128_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_env_118_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_nextMacroScope_119_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_ngen_120_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_auxDeclNGen_121_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_153_, 5, v_cache_122_);
lean_ctor_set(v_reuseFailAlloc_153_, 6, v_recordedDeps_123_);
lean_ctor_set(v_reuseFailAlloc_153_, 7, v_messages_124_);
lean_ctor_set(v_reuseFailAlloc_153_, 8, v_infoState_125_);
lean_ctor_set(v_reuseFailAlloc_153_, 9, v_snapshotTasks_126_);
v___x_148_ = v_reuseFailAlloc_153_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_st_ref_put(v___y_108_, v___x_148_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_135_);
v___x_151_ = v___x_114_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_135_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_158_, lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_158_, v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_cls_178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_180_ = l_Lean_Name_append(v___x_179_, v_cls_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_184_, lean_object* v_x_185_, lean_object* v_c_u2081_186_, lean_object* v_b_187_, lean_object* v_c_u2082_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_toCold_200_; lean_object* v_options_201_; lean_object* v_p_202_; lean_object* v_d_203_; lean_object* v_p_204_; lean_object* v_inheritedTraceOptions_205_; uint8_t v_hasTrace_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_d_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_p_213_; 
v_toCold_200_ = lean_ctor_get(v_a_197_, 0);
v_options_201_ = lean_ctor_get(v_toCold_200_, 2);
v_p_202_ = lean_ctor_get(v_c_u2081_186_, 0);
v_d_203_ = lean_ctor_get(v_c_u2082_188_, 0);
v_p_204_ = lean_ctor_get(v_c_u2082_188_, 1);
v_inheritedTraceOptions_205_ = lean_ctor_get(v_toCold_200_, 11);
v_hasTrace_206_ = lean_ctor_get_uint8(v_options_201_, sizeof(void*)*1);
v___x_207_ = lean_int_mul(v_a_184_, v_d_203_);
v___x_208_ = lean_nat_abs(v___x_207_);
lean_dec(v___x_207_);
v_d_209_ = lean_nat_to_int(v___x_208_);
lean_inc_ref(v_p_204_);
v___x_210_ = l_Int_Internal_Linear_Poly_mul(v_p_204_, v_a_184_);
v___x_211_ = lean_int_neg(v_b_187_);
lean_inc_ref(v_p_202_);
v___x_212_ = l_Int_Internal_Linear_Poly_mul(v_p_202_, v___x_211_);
lean_dec(v___x_211_);
v_p_213_ = l_Int_Internal_Linear_Poly_combine(v___x_210_, v___x_212_);
if (v_hasTrace_206_ == 0)
{
goto v___jp_214_;
}
else
{
lean_object* v_cls_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_cls_219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_220_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_221_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_205_, v_options_201_, v___x_220_);
if (v___x_221_ == 0)
{
goto v___jp_214_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_185_, v_a_189_, v_a_197_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc_ref(v_c_u2081_186_);
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_186_, v_a_189_, v_a_197_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
lean_inc_ref(v_c_u2082_188_);
v___x_226_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_188_, v_a_189_, v_a_197_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_MessageData_ofExpr(v_a_223_);
v___x_229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_225_);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_229_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_227_);
v___x_234_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_219_, v___x_233_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_dec_ref_known(v___x_234_, 1);
goto v___jp_214_;
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_p_213_);
lean_dec(v_d_209_);
lean_dec_ref(v_c_u2082_188_);
lean_dec_ref(v_c_u2081_186_);
lean_dec(v_x_185_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_225_);
lean_dec(v_a_223_);
lean_dec_ref(v_p_213_);
lean_dec(v_d_209_);
lean_dec_ref(v_c_u2082_188_);
lean_dec_ref(v_c_u2081_186_);
lean_dec(v_x_185_);
v_a_243_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_226_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_226_);
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
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_223_);
lean_dec_ref(v_p_213_);
lean_dec(v_d_209_);
lean_dec_ref(v_c_u2082_188_);
lean_dec_ref(v_c_u2081_186_);
lean_dec(v_x_185_);
v_a_251_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_224_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_224_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_p_213_);
lean_dec(v_d_209_);
lean_dec_ref(v_c_u2082_188_);
lean_dec_ref(v_c_u2081_186_);
lean_dec(v_x_185_);
v_a_259_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_222_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_222_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_215_, 0, v_x_185_);
lean_ctor_set(v___x_215_, 1, v_c_u2081_186_);
lean_ctor_set(v___x_215_, 2, v_c_u2082_188_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v_d_209_);
lean_ctor_set(v___x_217_, 1, v_p_213_);
lean_ctor_set(v___x_217_, 2, v___x_215_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_267_, lean_object* v_x_268_, lean_object* v_c_u2081_269_, lean_object* v_b_270_, lean_object* v_c_u2082_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_267_, v_x_268_, v_c_u2081_269_, v_b_270_, v_c_u2082_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec(v_a_272_);
lean_dec(v_b_270_);
lean_dec(v_a_267_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_284_, v_msg_285_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_298_, v_msg_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec(v___y_300_);
return v_res_311_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_maxRecDepthErrorMessage;
v___x_318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_320_ = l_Lean_MessageData_ofFormat(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_322_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_323_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_324_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_ref_324_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_332_, lean_object* v_ref_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_333_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_346_, lean_object* v_ref_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_346_, v_ref_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec(v___y_348_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_p_372_; lean_object* v_toCold_373_; lean_object* v_currRecDepth_374_; lean_object* v_ref_375_; uint16_t v_optionFlags_376_; uint8_t v_suppressElabErrors_377_; uint8_t v_checkDeprecated_378_; uint8_t v_isRecordingDeps_379_; lean_object* v_maxRecDepth_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_p_372_ = lean_ctor_get(v_c_360_, 1);
v_toCold_373_ = lean_ctor_get(v_a_369_, 0);
lean_inc_ref(v_toCold_373_);
v_currRecDepth_374_ = lean_ctor_get(v_a_369_, 1);
lean_inc(v_currRecDepth_374_);
v_ref_375_ = lean_ctor_get(v_a_369_, 2);
lean_inc(v_ref_375_);
v_optionFlags_376_ = lean_ctor_get_uint16(v_a_369_, sizeof(void*)*3);
v_suppressElabErrors_377_ = lean_ctor_get_uint8(v_a_369_, sizeof(void*)*3 + 2);
v_checkDeprecated_378_ = lean_ctor_get_uint8(v_a_369_, sizeof(void*)*3 + 3);
v_isRecordingDeps_379_ = lean_ctor_get_uint8(v_a_369_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_369_);
v_maxRecDepth_411_ = lean_ctor_get(v_toCold_373_, 3);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_nat_dec_eq(v_maxRecDepth_411_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_eq(v_currRecDepth_374_, v_maxRecDepth_411_);
if (v___x_414_ == 0)
{
goto v___jp_380_;
}
else
{
lean_object* v___x_415_; 
lean_dec(v_currRecDepth_374_);
lean_dec_ref(v_toCold_373_);
lean_dec_ref(v_c_360_);
v___x_415_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_375_);
return v___x_415_;
}
}
else
{
goto v___jp_380_;
}
v___jp_380_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_currRecDepth_374_, v___x_381_);
lean_dec(v_currRecDepth_374_);
v___x_383_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_383_, 0, v_toCold_373_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_ctor_set(v___x_383_, 2, v_ref_375_);
lean_ctor_set_uint16(v___x_383_, sizeof(void*)*3, v_optionFlags_376_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*3 + 2, v_suppressElabErrors_377_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*3 + 3, v_checkDeprecated_378_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*3 + 4, v_isRecordingDeps_379_);
lean_inc_ref(v_p_372_);
v___x_384_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_372_, v_a_361_, v___x_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_402_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_402_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
if (lean_obj_tag(v_a_385_) == 1)
{
lean_object* v_val_389_; lean_object* v_snd_390_; lean_object* v_snd_391_; lean_object* v_fst_392_; lean_object* v_fst_393_; lean_object* v_p_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_del_object(v___x_387_);
v_val_389_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v_a_385_, 1);
v_snd_390_ = lean_ctor_get(v_val_389_, 1);
lean_inc(v_snd_390_);
v_snd_391_ = lean_ctor_get(v_snd_390_, 1);
lean_inc(v_snd_391_);
v_fst_392_ = lean_ctor_get(v_val_389_, 0);
lean_inc(v_fst_392_);
lean_dec(v_val_389_);
v_fst_393_ = lean_ctor_get(v_snd_390_, 0);
lean_inc(v_fst_393_);
lean_dec(v_snd_390_);
v_p_394_ = lean_ctor_get(v_snd_391_, 0);
v___x_395_ = l_Int_Internal_Linear_Poly_coeff(v_p_394_, v_fst_393_);
v___x_396_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_395_, v_fst_393_, v_snd_391_, v_fst_392_, v_c_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v___x_383_, v_a_370_);
lean_dec(v_fst_392_);
lean_dec(v___x_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_c_360_ = v_a_397_;
v_a_369_ = v___x_383_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_383_, 3);
return v___x_396_;
}
}
else
{
lean_object* v___x_400_; 
lean_dec(v_a_385_);
lean_dec_ref_known(v___x_383_, 3);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_c_360_);
v___x_400_ = v___x_387_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_c_360_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref_known(v___x_383_, 3);
lean_dec_ref(v_c_360_);
v_a_403_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_384_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_384_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_429_, lean_object* v_v_430_, lean_object* v_s_431_){
_start:
{
lean_object* v_vars_432_; lean_object* v_varMap_433_; lean_object* v_varsHistory_434_; lean_object* v_natToIntMap_435_; lean_object* v_natDef_436_; lean_object* v_dvds_437_; lean_object* v_lowers_438_; lean_object* v_uppers_439_; lean_object* v_diseqs_440_; lean_object* v_elimEqs_441_; lean_object* v_elimStack_442_; lean_object* v_occurs_443_; lean_object* v_assignment_444_; lean_object* v_nextCnstrId_445_; uint8_t v_caseSplits_446_; lean_object* v_steps_447_; lean_object* v_penalties_448_; lean_object* v_numReorderRequests_449_; lean_object* v_conflict_x3f_450_; lean_object* v_diseqSplits_451_; lean_object* v_divMod_452_; uint8_t v_usedCommRing_453_; lean_object* v_nonlinearOccs_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_463_; 
v_vars_432_ = lean_ctor_get(v_s_431_, 0);
v_varMap_433_ = lean_ctor_get(v_s_431_, 1);
v_varsHistory_434_ = lean_ctor_get(v_s_431_, 2);
v_natToIntMap_435_ = lean_ctor_get(v_s_431_, 3);
v_natDef_436_ = lean_ctor_get(v_s_431_, 4);
v_dvds_437_ = lean_ctor_get(v_s_431_, 5);
v_lowers_438_ = lean_ctor_get(v_s_431_, 6);
v_uppers_439_ = lean_ctor_get(v_s_431_, 7);
v_diseqs_440_ = lean_ctor_get(v_s_431_, 8);
v_elimEqs_441_ = lean_ctor_get(v_s_431_, 9);
v_elimStack_442_ = lean_ctor_get(v_s_431_, 10);
v_occurs_443_ = lean_ctor_get(v_s_431_, 11);
v_assignment_444_ = lean_ctor_get(v_s_431_, 12);
v_nextCnstrId_445_ = lean_ctor_get(v_s_431_, 13);
v_caseSplits_446_ = lean_ctor_get_uint8(v_s_431_, sizeof(void*)*21);
v_steps_447_ = lean_ctor_get(v_s_431_, 14);
v_penalties_448_ = lean_ctor_get(v_s_431_, 15);
v_numReorderRequests_449_ = lean_ctor_get(v_s_431_, 16);
v_conflict_x3f_450_ = lean_ctor_get(v_s_431_, 17);
v_diseqSplits_451_ = lean_ctor_get(v_s_431_, 18);
v_divMod_452_ = lean_ctor_get(v_s_431_, 19);
v_usedCommRing_453_ = lean_ctor_get_uint8(v_s_431_, sizeof(void*)*21 + 1);
v_nonlinearOccs_454_ = lean_ctor_get(v_s_431_, 20);
v_isSharedCheck_463_ = !lean_is_exclusive(v_s_431_);
if (v_isSharedCheck_463_ == 0)
{
v___x_456_ = v_s_431_;
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_nonlinearOccs_454_);
lean_inc(v_divMod_452_);
lean_inc(v_diseqSplits_451_);
lean_inc(v_conflict_x3f_450_);
lean_inc(v_numReorderRequests_449_);
lean_inc(v_penalties_448_);
lean_inc(v_steps_447_);
lean_inc(v_nextCnstrId_445_);
lean_inc(v_assignment_444_);
lean_inc(v_occurs_443_);
lean_inc(v_elimStack_442_);
lean_inc(v_elimEqs_441_);
lean_inc(v_diseqs_440_);
lean_inc(v_uppers_439_);
lean_inc(v_lowers_438_);
lean_inc(v_dvds_437_);
lean_inc(v_natDef_436_);
lean_inc(v_natToIntMap_435_);
lean_inc(v_varsHistory_434_);
lean_inc(v_varMap_433_);
lean_inc(v_vars_432_);
lean_dec(v_s_431_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_a_429_);
v___x_459_ = l_Lean_PersistentArray_set___redArg(v_dvds_437_, v_v_430_, v___x_458_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 5, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_vars_432_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_varMap_433_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_varsHistory_434_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_natToIntMap_435_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_natDef_436_);
lean_ctor_set(v_reuseFailAlloc_462_, 5, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 6, v_lowers_438_);
lean_ctor_set(v_reuseFailAlloc_462_, 7, v_uppers_439_);
lean_ctor_set(v_reuseFailAlloc_462_, 8, v_diseqs_440_);
lean_ctor_set(v_reuseFailAlloc_462_, 9, v_elimEqs_441_);
lean_ctor_set(v_reuseFailAlloc_462_, 10, v_elimStack_442_);
lean_ctor_set(v_reuseFailAlloc_462_, 11, v_occurs_443_);
lean_ctor_set(v_reuseFailAlloc_462_, 12, v_assignment_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 13, v_nextCnstrId_445_);
lean_ctor_set(v_reuseFailAlloc_462_, 14, v_steps_447_);
lean_ctor_set(v_reuseFailAlloc_462_, 15, v_penalties_448_);
lean_ctor_set(v_reuseFailAlloc_462_, 16, v_numReorderRequests_449_);
lean_ctor_set(v_reuseFailAlloc_462_, 17, v_conflict_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_462_, 18, v_diseqSplits_451_);
lean_ctor_set(v_reuseFailAlloc_462_, 19, v_divMod_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 20, v_nonlinearOccs_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*21, v_caseSplits_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*21 + 1, v_usedCommRing_453_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_464_, lean_object* v_v_465_, lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_464_, v_v_465_, v_s_466_);
lean_dec(v_v_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_468_, lean_object* v_s_469_){
_start:
{
lean_object* v_vars_470_; lean_object* v_varMap_471_; lean_object* v_varsHistory_472_; lean_object* v_natToIntMap_473_; lean_object* v_natDef_474_; lean_object* v_dvds_475_; lean_object* v_lowers_476_; lean_object* v_uppers_477_; lean_object* v_diseqs_478_; lean_object* v_elimEqs_479_; lean_object* v_elimStack_480_; lean_object* v_occurs_481_; lean_object* v_assignment_482_; lean_object* v_nextCnstrId_483_; uint8_t v_caseSplits_484_; lean_object* v_steps_485_; lean_object* v_penalties_486_; lean_object* v_numReorderRequests_487_; lean_object* v_conflict_x3f_488_; lean_object* v_diseqSplits_489_; lean_object* v_divMod_490_; uint8_t v_usedCommRing_491_; lean_object* v_nonlinearOccs_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_501_; 
v_vars_470_ = lean_ctor_get(v_s_469_, 0);
v_varMap_471_ = lean_ctor_get(v_s_469_, 1);
v_varsHistory_472_ = lean_ctor_get(v_s_469_, 2);
v_natToIntMap_473_ = lean_ctor_get(v_s_469_, 3);
v_natDef_474_ = lean_ctor_get(v_s_469_, 4);
v_dvds_475_ = lean_ctor_get(v_s_469_, 5);
v_lowers_476_ = lean_ctor_get(v_s_469_, 6);
v_uppers_477_ = lean_ctor_get(v_s_469_, 7);
v_diseqs_478_ = lean_ctor_get(v_s_469_, 8);
v_elimEqs_479_ = lean_ctor_get(v_s_469_, 9);
v_elimStack_480_ = lean_ctor_get(v_s_469_, 10);
v_occurs_481_ = lean_ctor_get(v_s_469_, 11);
v_assignment_482_ = lean_ctor_get(v_s_469_, 12);
v_nextCnstrId_483_ = lean_ctor_get(v_s_469_, 13);
v_caseSplits_484_ = lean_ctor_get_uint8(v_s_469_, sizeof(void*)*21);
v_steps_485_ = lean_ctor_get(v_s_469_, 14);
v_penalties_486_ = lean_ctor_get(v_s_469_, 15);
v_numReorderRequests_487_ = lean_ctor_get(v_s_469_, 16);
v_conflict_x3f_488_ = lean_ctor_get(v_s_469_, 17);
v_diseqSplits_489_ = lean_ctor_get(v_s_469_, 18);
v_divMod_490_ = lean_ctor_get(v_s_469_, 19);
v_usedCommRing_491_ = lean_ctor_get_uint8(v_s_469_, sizeof(void*)*21 + 1);
v_nonlinearOccs_492_ = lean_ctor_get(v_s_469_, 20);
v_isSharedCheck_501_ = !lean_is_exclusive(v_s_469_);
if (v_isSharedCheck_501_ == 0)
{
v___x_494_ = v_s_469_;
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_nonlinearOccs_492_);
lean_inc(v_divMod_490_);
lean_inc(v_diseqSplits_489_);
lean_inc(v_conflict_x3f_488_);
lean_inc(v_numReorderRequests_487_);
lean_inc(v_penalties_486_);
lean_inc(v_steps_485_);
lean_inc(v_nextCnstrId_483_);
lean_inc(v_assignment_482_);
lean_inc(v_occurs_481_);
lean_inc(v_elimStack_480_);
lean_inc(v_elimEqs_479_);
lean_inc(v_diseqs_478_);
lean_inc(v_uppers_477_);
lean_inc(v_lowers_476_);
lean_inc(v_dvds_475_);
lean_inc(v_natDef_474_);
lean_inc(v_natToIntMap_473_);
lean_inc(v_varsHistory_472_);
lean_inc(v_varMap_471_);
lean_inc(v_vars_470_);
lean_dec(v_s_469_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = lean_box(0);
v___x_497_ = l_Lean_PersistentArray_set___redArg(v_dvds_475_, v_v_468_, v___x_496_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 5, v___x_497_);
v___x_499_ = v___x_494_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_vars_470_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_varMap_471_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_varsHistory_472_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_natToIntMap_473_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_natDef_474_);
lean_ctor_set(v_reuseFailAlloc_500_, 5, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 6, v_lowers_476_);
lean_ctor_set(v_reuseFailAlloc_500_, 7, v_uppers_477_);
lean_ctor_set(v_reuseFailAlloc_500_, 8, v_diseqs_478_);
lean_ctor_set(v_reuseFailAlloc_500_, 9, v_elimEqs_479_);
lean_ctor_set(v_reuseFailAlloc_500_, 10, v_elimStack_480_);
lean_ctor_set(v_reuseFailAlloc_500_, 11, v_occurs_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 12, v_assignment_482_);
lean_ctor_set(v_reuseFailAlloc_500_, 13, v_nextCnstrId_483_);
lean_ctor_set(v_reuseFailAlloc_500_, 14, v_steps_485_);
lean_ctor_set(v_reuseFailAlloc_500_, 15, v_penalties_486_);
lean_ctor_set(v_reuseFailAlloc_500_, 16, v_numReorderRequests_487_);
lean_ctor_set(v_reuseFailAlloc_500_, 17, v_conflict_x3f_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 18, v_diseqSplits_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 19, v_divMod_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 20, v_nonlinearOccs_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*21, v_caseSplits_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*21 + 1, v_usedCommRing_491_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_502_, lean_object* v_s_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_502_, v_s_503_);
lean_dec(v_v_502_);
return v_res_504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_514_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_515_ = l_Lean_Name_append(v___x_514_, v___x_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v_toCold_681_; lean_object* v_currRecDepth_682_; lean_object* v_ref_683_; uint16_t v_optionFlags_684_; uint8_t v_suppressElabErrors_685_; uint8_t v_checkDeprecated_686_; uint8_t v_isRecordingDeps_687_; lean_object* v_options_688_; lean_object* v_maxRecDepth_689_; lean_object* v_inheritedTraceOptions_690_; lean_object* v___x_691_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_toCold_681_ = lean_ctor_get(v_a_525_, 0);
lean_inc_ref(v_toCold_681_);
v_currRecDepth_682_ = lean_ctor_get(v_a_525_, 1);
lean_inc(v_currRecDepth_682_);
v_ref_683_ = lean_ctor_get(v_a_525_, 2);
lean_inc(v_ref_683_);
v_optionFlags_684_ = lean_ctor_get_uint16(v_a_525_, sizeof(void*)*3);
v_suppressElabErrors_685_ = lean_ctor_get_uint8(v_a_525_, sizeof(void*)*3 + 2);
v_checkDeprecated_686_ = lean_ctor_get_uint8(v_a_525_, sizeof(void*)*3 + 3);
v_isRecordingDeps_687_ = lean_ctor_get_uint8(v_a_525_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_525_);
v_options_688_ = lean_ctor_get(v_toCold_681_, 2);
lean_inc_ref(v_options_688_);
v_maxRecDepth_689_ = lean_ctor_get(v_toCold_681_, 3);
v_inheritedTraceOptions_690_ = lean_ctor_get(v_toCold_681_, 11);
lean_inc_ref(v_inheritedTraceOptions_690_);
v___x_691_ = lean_box(0);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_nat_dec_eq(v_maxRecDepth_689_, v___x_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_eq(v_currRecDepth_682_, v_maxRecDepth_689_);
if (v___x_873_ == 0)
{
goto v___jp_830_;
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v_inheritedTraceOptions_690_);
lean_dec_ref(v_options_688_);
lean_dec(v_currRecDepth_682_);
lean_dec_ref(v_toCold_681_);
lean_dec_ref(v_c_516_);
v___x_874_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_683_);
return v___x_874_;
}
}
else
{
goto v___jp_830_;
}
v___jp_528_:
{
lean_object* v_p_536_; lean_object* v___x_537_; 
v_p_536_ = lean_ctor_get(v___y_529_, 1);
lean_inc_ref(v_p_536_);
lean_dec_ref(v___y_529_);
v___x_537_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_536_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec_ref(v___y_534_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_537_, 1);
v___x_538_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_539_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_538_, v___y_530_, v___y_531_);
return v___x_539_;
}
else
{
lean_dec_ref(v___y_530_);
return v___x_537_;
}
}
v___jp_540_:
{
if (lean_obj_tag(v___y_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_p_563_; 
lean_dec(v___y_541_);
v_val_562_ = lean_ctor_get(v___y_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___y_561_, 1);
v_p_563_ = lean_ctor_get(v_val_562_, 1);
lean_inc_ref(v_p_563_);
if (lean_obj_tag(v_p_563_) == 1)
{
lean_object* v_d_564_; lean_object* v_k_565_; lean_object* v_p_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_621_; 
v_d_564_ = lean_ctor_get(v_val_562_, 0);
v_k_565_ = lean_ctor_get(v_p_563_, 0);
v_p_566_ = lean_ctor_get(v_p_563_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_p_563_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_p_563_, 1);
lean_dec(v_unused_622_);
v___x_568_ = v_p_563_;
v_isShared_569_ = v_isSharedCheck_621_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_p_566_);
lean_inc(v_k_565_);
lean_dec(v_p_563_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_621_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_snd_573_; lean_object* v_fst_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_620_; 
v___x_570_ = lean_int_mul(v___y_552_, v_d_564_);
v___x_571_ = lean_int_mul(v_k_565_, v___y_546_);
v___x_572_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_570_, v___x_571_);
lean_dec(v___x_571_);
lean_dec(v___x_570_);
v_snd_573_ = lean_ctor_get(v___x_572_, 1);
v_fst_574_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_620_ == 0)
{
v___x_576_ = v___x_572_;
v_isShared_577_ = v_isSharedCheck_620_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snd_573_);
lean_inc(v_fst_574_);
lean_dec(v___x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_620_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_619_; 
v_fst_578_ = lean_ctor_get(v_snd_573_, 0);
v_snd_579_ = lean_ctor_get(v_snd_573_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_snd_573_);
if (v_isSharedCheck_619_ == 0)
{
v___x_581_ = v_snd_573_;
v_isShared_582_ = v_isSharedCheck_619_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_inc(v_fst_578_);
lean_dec(v_snd_573_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_619_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_583_ = lean_int_mul(v_fst_578_, v_d_564_);
lean_dec(v_fst_578_);
lean_inc_ref(v___y_542_);
v___x_584_ = l_Int_Internal_Linear_Poly_mul(v___y_542_, v___x_583_);
lean_dec(v___x_583_);
v___x_585_ = lean_int_mul(v_snd_579_, v___y_546_);
lean_dec(v_snd_579_);
lean_inc_ref(v_p_566_);
v___x_586_ = l_Int_Internal_Linear_Poly_mul(v_p_566_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_int_mul(v___y_546_, v_d_564_);
lean_dec(v___y_546_);
v___x_588_ = l_Int_Internal_Linear_Poly_combine(v___x_584_, v___x_586_);
lean_inc(v_fst_574_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 2, v___x_588_);
lean_ctor_set(v___x_568_, 1, v___y_545_);
lean_ctor_set(v___x_568_, 0, v_fst_574_);
v___x_590_ = v___x_568_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___y_545_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_588_);
v___x_590_ = v_reuseFailAlloc_618_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
lean_inc(v_val_562_);
lean_inc_ref(v___y_557_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 5);
lean_ctor_set(v___x_581_, 1, v_val_562_);
lean_ctor_set(v___x_581_, 0, v___y_557_);
v___x_592_ = v___x_581_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___y_557_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_val_562_);
v___x_592_ = v_reuseFailAlloc_617_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_594_, 0, v___x_587_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
lean_ctor_set(v___x_594_, 2, v___x_592_);
lean_ctor_set(v___x_594_, 3, v___x_593_);
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_596_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_595_, v___y_547_, v___y_543_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; 
lean_dec_ref_known(v___x_596_, 1);
lean_inc_ref(v___y_556_);
v___x_597_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_594_, v___y_543_, v___y_558_, v___y_544_, v___y_559_, v___y_560_, v___y_550_, v___y_553_, v___y_554_, v___y_556_, v___y_555_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec_ref_known(v___x_597_, 1);
v___x_598_ = l_Int_Internal_Linear_Poly_mul(v___y_542_, v_k_565_);
lean_dec(v_k_565_);
v___x_599_ = lean_int_neg(v___y_552_);
lean_dec(v___y_552_);
v___x_600_ = l_Int_Internal_Linear_Poly_mul(v_p_566_, v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = l_Int_Internal_Linear_Poly_combine(v___x_598_, v___x_600_);
lean_inc(v_val_562_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 6);
lean_ctor_set(v___x_576_, 1, v_val_562_);
lean_ctor_set(v___x_576_, 0, v___y_557_);
v___x_603_ = v___x_576_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___y_557_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_val_562_);
v___x_603_ = v_reuseFailAlloc_616_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_isSharedCheck_611_ = !lean_is_exclusive(v_val_562_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_612_ = lean_ctor_get(v_val_562_, 3);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_val_562_, 2);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_val_562_, 1);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_val_562_, 0);
lean_dec(v_unused_615_);
v___x_605_ = v_val_562_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_dec(v_val_562_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 3, v___x_593_);
lean_ctor_set(v___x_605_, 2, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_601_);
lean_ctor_set(v___x_605_, 0, v_fst_574_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___x_593_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v_c_516_ = v___x_608_;
v_a_517_ = v___y_543_;
v_a_518_ = v___y_558_;
v_a_519_ = v___y_544_;
v_a_520_ = v___y_559_;
v_a_521_ = v___y_560_;
v_a_522_ = v___y_550_;
v_a_523_ = v___y_553_;
v_a_524_ = v___y_554_;
v_a_525_ = v___y_556_;
v_a_526_ = v___y_555_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_576_);
lean_dec(v_fst_574_);
lean_dec_ref(v_p_566_);
lean_dec(v_k_565_);
lean_dec(v_val_562_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_542_);
return v___x_597_;
}
}
else
{
lean_dec_ref_known(v___x_594_, 4);
lean_del_object(v___x_576_);
lean_dec(v_fst_574_);
lean_dec_ref(v_p_566_);
lean_dec(v_k_565_);
lean_dec(v_val_562_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_542_);
return v___x_596_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec_ref(v_p_563_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_542_);
v___x_623_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_562_, v___y_543_, v___y_558_, v___y_544_, v___y_559_, v___y_560_, v___y_550_, v___y_553_, v___y_554_, v___y_556_, v___y_555_);
lean_dec_ref(v___y_556_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v___y_561_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_542_);
v___x_624_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v___y_557_, v___y_543_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_toCold_625_; lean_object* v_options_626_; lean_object* v_a_627_; lean_object* v_inheritedTraceOptions_628_; uint8_t v_hasTrace_629_; lean_object* v___f_630_; 
v_toCold_625_ = lean_ctor_get(v___y_556_, 0);
v_options_626_ = lean_ctor_get(v_toCold_625_, 2);
v_a_627_ = lean_ctor_get(v___x_624_, 0);
lean_inc_n(v_a_627_, 2);
lean_dec_ref_known(v___x_624_, 1);
v_inheritedTraceOptions_628_ = lean_ctor_get(v_toCold_625_, 11);
v_hasTrace_629_ = lean_ctor_get_uint8(v_options_626_, sizeof(void*)*1);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_630_, 0, v_a_627_);
lean_closure_set(v___f_630_, 1, v___y_541_);
if (v_hasTrace_629_ == 0)
{
v___y_529_ = v_a_627_;
v___y_530_ = v___f_630_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_553_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_556_;
v___y_535_ = v___y_555_;
goto v___jp_528_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_631_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_548_);
lean_inc_ref(v___y_549_);
lean_inc_ref(v___y_551_);
v___x_632_ = l_Lean_Name_mkStr4(v___y_551_, v___y_549_, v___y_548_, v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_632_);
v___x_634_ = l_Lean_Name_append(v___x_633_, v___x_632_);
v___x_635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_628_, v_options_626_, v___x_634_);
lean_dec(v___x_634_);
if (v___x_635_ == 0)
{
lean_dec(v___x_632_);
v___y_529_ = v_a_627_;
v___y_530_ = v___f_630_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_553_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_556_;
v___y_535_ = v___y_555_;
goto v___jp_528_;
}
else
{
lean_object* v___x_636_; 
lean_inc(v_a_627_);
v___x_636_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_627_, v___y_543_, v___y_556_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_632_, v_a_637_, v___y_553_, v___y_554_, v___y_556_, v___y_555_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
v___y_529_ = v_a_627_;
v___y_530_ = v___f_630_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_553_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_556_;
v___y_535_ = v___y_555_;
goto v___jp_528_;
}
else
{
lean_dec_ref(v___f_630_);
lean_dec(v_a_627_);
lean_dec_ref(v___y_556_);
return v___x_638_;
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_632_);
lean_dec_ref(v___f_630_);
lean_dec(v_a_627_);
lean_dec_ref(v___y_556_);
v_a_639_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_636_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_636_);
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
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v___y_556_);
lean_dec(v___y_541_);
v_a_647_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_624_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_624_);
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
v___jp_655_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___y_656_);
v___x_668_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_667_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec_ref(v___y_665_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_677_);
v___x_670_ = v___x_668_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_668_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
return v___x_668_;
}
}
v___jp_678_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
v___jp_692_:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_702_, v___y_710_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_dvds_714_; lean_object* v_size_715_; uint8_t v___x_716_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v_dvds_714_ = lean_ctor_get(v_a_713_, 5);
lean_inc_ref(v_dvds_714_);
lean_dec(v_a_713_);
v_size_715_ = lean_ctor_get(v_dvds_714_, 2);
v___x_716_ = lean_nat_dec_lt(v___y_694_, v_size_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_dvds_714_);
v___x_717_ = l_outOfBounds___redArg(v___x_691_);
lean_inc(v___y_694_);
v___y_541_ = v___y_694_;
v___y_542_ = v___y_693_;
v___y_543_ = v___y_702_;
v___y_544_ = v___y_704_;
v___y_545_ = v___y_694_;
v___y_546_ = v___y_701_;
v___y_547_ = v___y_700_;
v___y_548_ = v___y_696_;
v___y_549_ = v___y_697_;
v___y_550_ = v___y_707_;
v___y_551_ = v___y_698_;
v___y_552_ = v___y_695_;
v___y_553_ = v___y_708_;
v___y_554_ = v___y_709_;
v___y_555_ = v___y_711_;
v___y_556_ = v___y_710_;
v___y_557_ = v___y_699_;
v___y_558_ = v___y_703_;
v___y_559_ = v___y_705_;
v___y_560_ = v___y_706_;
v___y_561_ = v___x_717_;
goto v___jp_540_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_PersistentArray_get_x21___redArg(v___x_691_, v_dvds_714_, v___y_694_);
lean_dec_ref(v_dvds_714_);
lean_inc(v___y_694_);
v___y_541_ = v___y_694_;
v___y_542_ = v___y_693_;
v___y_543_ = v___y_702_;
v___y_544_ = v___y_704_;
v___y_545_ = v___y_694_;
v___y_546_ = v___y_701_;
v___y_547_ = v___y_700_;
v___y_548_ = v___y_696_;
v___y_549_ = v___y_697_;
v___y_550_ = v___y_707_;
v___y_551_ = v___y_698_;
v___y_552_ = v___y_695_;
v___y_553_ = v___y_708_;
v___y_554_ = v___y_709_;
v___y_555_ = v___y_711_;
v___y_556_ = v___y_710_;
v___y_557_ = v___y_699_;
v___y_558_ = v___y_703_;
v___y_559_ = v___y_705_;
v___y_560_ = v___y_706_;
v___y_561_ = v___x_718_;
goto v___jp_540_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v___y_710_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
v_a_719_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_712_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_712_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_516_);
lean_inc_ref(v___y_739_);
v___x_742_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_741_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v_d_745_; lean_object* v_p_746_; uint8_t v___x_747_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_a_743_);
v_d_745_ = lean_ctor_get(v___x_744_, 0);
v_p_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_d_745_);
v___x_747_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_745_, v_p_746_);
if (v___x_747_ == 0)
{
uint8_t v___x_748_; 
v___x_748_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v___x_744_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_750_ = lean_int_dec_eq(v_d_745_, v___x_749_);
if (v___x_750_ == 0)
{
if (lean_obj_tag(v_p_746_) == 1)
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_p_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
lean_inc(v_d_745_);
v_k_751_ = lean_ctor_get(v_p_746_, 0);
lean_inc(v_k_751_);
v_v_752_ = lean_ctor_get(v_p_746_, 1);
lean_inc_n(v_v_752_, 2);
v_p_753_ = lean_ctor_get(v_p_746_, 2);
lean_inc_ref(v_p_753_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_754_, 0, v_v_752_);
lean_inc_ref(v___x_744_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v___x_744_, v___y_731_, v___y_739_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = 0;
v___x_758_ = lean_unbox(v_a_756_);
lean_dec(v_a_756_);
v___x_759_ = l_Lean_instBEqLBool_beq(v___x_758_, v___x_757_);
if (v___x_759_ == 0)
{
v___y_693_ = v_p_753_;
v___y_694_ = v_v_752_;
v___y_695_ = v_k_751_;
v___y_696_ = v___y_728_;
v___y_697_ = v___y_729_;
v___y_698_ = v___y_730_;
v___y_699_ = v___x_744_;
v___y_700_ = v___f_754_;
v___y_701_ = v_d_745_;
v___y_702_ = v___y_731_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_733_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_735_;
v___y_707_ = v___y_736_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_739_;
v___y_711_ = v___y_740_;
goto v___jp_692_;
}
else
{
lean_object* v___x_760_; 
lean_inc(v_v_752_);
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_752_, v___y_731_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref_known(v___x_760_, 1);
v___y_693_ = v_p_753_;
v___y_694_ = v_v_752_;
v___y_695_ = v_k_751_;
v___y_696_ = v___y_728_;
v___y_697_ = v___y_729_;
v___y_698_ = v___y_730_;
v___y_699_ = v___x_744_;
v___y_700_ = v___f_754_;
v___y_701_ = v_d_745_;
v___y_702_ = v___y_731_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_733_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_735_;
v___y_707_ = v___y_736_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_739_;
v___y_711_ = v___y_740_;
goto v___jp_692_;
}
else
{
lean_dec_ref(v___f_754_);
lean_dec_ref(v_p_753_);
lean_dec(v_v_752_);
lean_dec(v_k_751_);
lean_dec(v_d_745_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
return v___x_760_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___f_754_);
lean_dec_ref(v_p_753_);
lean_dec(v_v_752_);
lean_dec(v_k_751_);
lean_dec(v_d_745_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
v_a_761_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_755_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_755_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v___x_744_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec_ref(v___y_739_);
return v___x_769_;
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_inc_ref(v_p_746_);
v___x_770_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_744_);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v_p_746_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_ctor_set(v___x_771_, 2, v___x_691_);
lean_inc(v___y_740_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc(v___y_731_);
v___x_772_ = lean_grind_cutsat_assert_eq(v___x_771_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_772_, 0);
lean_dec(v_unused_781_);
v___x_774_ = v___x_772_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_772_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_box(0);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
return v___x_772_;
}
}
}
else
{
lean_object* v_toCold_782_; lean_object* v_options_783_; uint8_t v_hasTrace_784_; 
v_toCold_782_ = lean_ctor_get(v___y_739_, 0);
v_options_783_ = lean_ctor_get(v_toCold_782_, 2);
v_hasTrace_784_ = lean_ctor_get_uint8(v_options_783_, sizeof(void*)*1);
if (v_hasTrace_784_ == 0)
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
goto v___jp_678_;
}
else
{
lean_object* v_inheritedTraceOptions_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_inheritedTraceOptions_785_ = lean_ctor_get(v_toCold_782_, 11);
v___x_786_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_728_);
lean_inc_ref(v___y_729_);
lean_inc_ref(v___y_730_);
v___x_787_ = l_Lean_Name_mkStr4(v___y_730_, v___y_729_, v___y_728_, v___x_786_);
v___x_788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_787_);
v___x_789_ = l_Lean_Name_append(v___x_788_, v___x_787_);
v___x_790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_785_, v_options_783_, v___x_789_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
lean_dec(v___x_787_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
goto v___jp_678_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_744_, v___y_731_, v___y_739_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_787_, v_a_792_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec_ref(v___y_739_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_dec_ref_known(v___x_793_, 1);
goto v___jp_678_;
}
else
{
return v___x_793_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v___x_787_);
lean_dec_ref(v___y_739_);
v_a_794_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_791_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_791_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_802_; lean_object* v_options_803_; uint8_t v_hasTrace_804_; 
v_toCold_802_ = lean_ctor_get(v___y_739_, 0);
v_options_803_ = lean_ctor_get(v_toCold_802_, 2);
v_hasTrace_804_ = lean_ctor_get_uint8(v_options_803_, sizeof(void*)*1);
if (v_hasTrace_804_ == 0)
{
v___y_656_ = v___x_744_;
v___y_657_ = v___y_731_;
v___y_658_ = v___y_732_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
goto v___jp_655_;
}
else
{
lean_object* v_inheritedTraceOptions_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_inheritedTraceOptions_805_ = lean_ctor_get(v_toCold_802_, 11);
v___x_806_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_728_);
lean_inc_ref(v___y_729_);
lean_inc_ref(v___y_730_);
v___x_807_ = l_Lean_Name_mkStr4(v___y_730_, v___y_729_, v___y_728_, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Name_append(v___x_808_, v___x_807_);
v___x_810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_805_, v_options_803_, v___x_809_);
lean_dec(v___x_809_);
if (v___x_810_ == 0)
{
lean_dec(v___x_807_);
v___y_656_ = v___x_744_;
v___y_657_ = v___y_731_;
v___y_658_ = v___y_732_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
goto v___jp_655_;
}
else
{
lean_object* v___x_811_; 
lean_inc_ref(v___x_744_);
v___x_811_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_744_, v___y_731_, v___y_739_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_807_, v_a_812_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_dec_ref_known(v___x_813_, 1);
v___y_656_ = v___x_744_;
v___y_657_ = v___y_731_;
v___y_658_ = v___y_732_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
goto v___jp_655_;
}
else
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
return v___x_813_;
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v___x_807_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___y_739_);
v_a_814_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_811_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_811_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v___y_739_);
v_a_822_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_742_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_742_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
v___jp_830_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_currRecDepth_682_, v___x_831_);
lean_dec(v_currRecDepth_682_);
v___x_833_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_833_, 0, v_toCold_681_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set(v___x_833_, 2, v_ref_683_);
lean_ctor_set_uint16(v___x_833_, sizeof(void*)*3, v_optionFlags_684_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*3 + 2, v_suppressElabErrors_685_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*3 + 3, v_checkDeprecated_686_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*3 + 4, v_isRecordingDeps_687_);
v___x_834_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_517_, v___x_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_862_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_862_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; 
v___x_839_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_839_ == 0)
{
uint8_t v_hasTrace_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_837_);
v_hasTrace_840_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
v___x_841_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_842_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_843_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_840_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_690_);
lean_dec_ref(v_options_688_);
v___y_728_ = v___x_843_;
v___y_729_ = v___x_842_;
v___y_730_ = v___x_841_;
v___y_731_ = v_a_517_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v___x_833_;
v___y_740_ = v_a_526_;
goto v___jp_727_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_845_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_690_, v_options_688_, v___x_845_);
lean_dec_ref(v_options_688_);
lean_dec_ref(v_inheritedTraceOptions_690_);
if (v___x_846_ == 0)
{
v___y_728_ = v___x_843_;
v___y_729_ = v___x_842_;
v___y_730_ = v___x_841_;
v___y_731_ = v_a_517_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v___x_833_;
v___y_740_ = v_a_526_;
goto v___jp_727_;
}
else
{
lean_object* v___x_847_; 
lean_inc_ref(v_c_516_);
v___x_847_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_516_, v_a_517_, v___x_833_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_844_, v_a_848_, v_a_523_, v_a_524_, v___x_833_, v_a_526_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_dec_ref_known(v___x_849_, 1);
v___y_728_ = v___x_843_;
v___y_729_ = v___x_842_;
v___y_730_ = v___x_841_;
v___y_731_ = v_a_517_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v___x_833_;
v___y_740_ = v_a_526_;
goto v___jp_727_;
}
else
{
lean_dec_ref_known(v___x_833_, 3);
lean_dec_ref(v_c_516_);
return v___x_849_;
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref_known(v___x_833_, 3);
lean_dec_ref(v_c_516_);
v_a_850_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_847_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec_ref_known(v___x_833_, 3);
lean_dec_ref(v_inheritedTraceOptions_690_);
lean_dec_ref(v_options_688_);
lean_dec_ref(v_c_516_);
v___x_858_ = lean_box(0);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_858_);
v___x_860_ = v___x_837_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref_known(v___x_833_, 3);
lean_dec_ref(v_inheritedTraceOptions_690_);
lean_dec_ref(v_options_688_);
lean_dec_ref(v_c_516_);
v_a_863_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_834_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_834_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_d_900_; lean_object* v_p_901_; lean_object* v___x_902_; 
v_d_900_ = lean_ctor_get(v_c_888_, 0);
v_p_901_ = lean_ctor_get(v_c_888_, 1);
lean_inc_ref(v_p_901_);
v___x_902_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_901_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
if (lean_obj_tag(v_a_903_) == 1)
{
lean_object* v_val_904_; lean_object* v_snd_905_; lean_object* v_fst_906_; lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_d_900_);
v_val_904_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_a_903_, 1);
v_snd_905_ = lean_ctor_get(v_val_904_, 1);
lean_inc(v_snd_905_);
v_fst_906_ = lean_ctor_get(v_val_904_, 0);
lean_inc(v_fst_906_);
lean_dec(v_val_904_);
v_fst_907_ = lean_ctor_get(v_snd_905_, 0);
lean_inc(v_fst_907_);
v_snd_908_ = lean_ctor_get(v_snd_905_, 1);
lean_inc(v_snd_908_);
lean_dec(v_snd_905_);
v___x_909_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_909_, 0, v_c_888_);
lean_ctor_set(v___x_909_, 1, v_fst_906_);
lean_ctor_set(v___x_909_, 2, v_fst_907_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_911_, 0, v_d_900_);
lean_ctor_set(v___x_911_, 1, v_snd_908_);
lean_ctor_set(v___x_911_, 2, v___x_909_);
lean_ctor_set(v___x_911_, 3, v___x_910_);
lean_inc_ref(v_a_897_);
v___x_912_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_911_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
lean_dec(v_a_903_);
lean_inc_ref(v_a_897_);
v___x_913_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_913_;
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v_c_888_);
v_a_914_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_902_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_902_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec(v_a_923_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_951_ = l_Lean_mkConst(v___x_950_, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_973_; 
lean_inc_ref(v_e_955_);
v___x_973_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_955_, v_a_963_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_Expr_cleanupAnnotations(v_a_974_);
lean_dec(v_a_974_);
v___x_976_ = l_Lean_Expr_isApp(v___x_975_);
if (v___x_976_ == 0)
{
lean_dec_ref(v___x_975_);
lean_dec_ref(v_e_955_);
goto v___jp_967_;
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_975_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v_e_955_);
goto v___jp_967_;
}
else
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_977_);
v___x_980_ = l_Lean_Expr_isApp(v___x_979_);
if (v___x_980_ == 0)
{
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v_e_955_);
goto v___jp_967_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_979_);
v___x_982_ = l_Lean_Expr_isApp(v___x_981_);
if (v___x_982_ == 0)
{
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v_e_955_);
goto v___jp_967_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_981_);
lean_dec_ref(v___x_981_);
v___x_984_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_985_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_984_);
lean_dec_ref(v___x_983_);
if (v___x_985_ == 0)
{
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v_e_955_);
goto v___jp_967_;
}
else
{
lean_object* v_arg_986_; lean_object* v_arg_987_; lean_object* v_arg_988_; lean_object* v___x_989_; 
v_arg_986_ = lean_ctor_get(v___x_975_, 1);
lean_inc_ref(v_arg_986_);
lean_dec_ref(v___x_975_);
v_arg_987_ = lean_ctor_get(v___x_977_, 1);
lean_inc_ref(v_arg_987_);
lean_dec_ref(v___x_977_);
v_arg_988_ = lean_ctor_get(v___x_979_, 1);
lean_inc_ref(v_arg_988_);
lean_dec_ref(v___x_979_);
v___x_989_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_988_, v_a_963_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1091_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1091_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1091_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v___x_995_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_999_; 
lean_del_object(v___x_992_);
lean_inc_ref(v_arg_987_);
v___x_999_ = l_Lean_Meta_getIntValue_x3f(v_arg_987_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
if (lean_obj_tag(v_a_1000_) == 1)
{
lean_object* v_val_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1067_; 
v_val_1001_ = lean_ctor_get(v_a_1000_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_a_1000_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1003_ = v_a_1000_;
v_isShared_1004_ = v_isSharedCheck_1067_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_val_1001_);
lean_dec(v_a_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1067_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; 
lean_inc_ref(v_e_955_);
v___x_1005_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_955_, v_a_956_, v_a_960_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; uint8_t v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_unbox(v_a_1006_);
lean_dec(v_a_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_del_object(v___x_1003_);
lean_dec(v_val_1001_);
lean_inc_ref(v_e_955_);
v___x_1008_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_955_, v_a_956_, v_a_960_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1034_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1034_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1034_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_unbox(v_a_1009_);
lean_dec(v_a_1009_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v___x_1014_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1018_; 
lean_del_object(v___x_1011_);
lean_inc_ref(v_e_955_);
v___x_1018_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_1021_ = l_Lean_eagerReflBoolTrue;
v___x_1022_ = l_Lean_Meta_mkOfEqFalseCore(v_e_955_, v_a_1019_);
v___x_1023_ = l_Lean_mkApp4(v___x_1020_, v_arg_987_, v_arg_986_, v___x_1021_, v___x_1022_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = l_Lean_Meta_Grind_pushNewFact(v___x_1023_, v___x_1024_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1025_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v_a_1026_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1018_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1018_);
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
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v_a_1035_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1008_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1008_);
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
else
{
lean_object* v___x_1043_; 
lean_dec_ref(v_arg_987_);
v___x_1043_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_986_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
lean_ctor_set(v___x_1003_, 0, v_e_955_);
v___x_1046_ = v___x_1003_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_e_955_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1048_, 0, v_val_1001_);
lean_ctor_set(v___x_1048_, 1, v_a_1044_);
lean_ctor_set(v___x_1048_, 2, v___x_1046_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
v___x_1049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1048_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1049_;
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_1003_);
lean_dec(v_val_1001_);
lean_dec_ref(v_e_955_);
v_a_1051_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1043_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_1003_);
lean_dec(v_val_1001_);
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v_a_1059_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1005_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1005_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_a_1000_);
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
v___x_1068_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1069_ = l_Lean_indentExpr(v_e_955_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_960_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; uint8_t v_verbose_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_verbose_1073_ = lean_ctor_get_uint8(v_a_1072_, 0);
lean_dec(v_a_1072_);
if (v_verbose_1073_ == 0)
{
lean_dec_ref_known(v___x_1070_, 2);
goto v___jp_970_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Meta_Sym_reportIssue(v___x_1070_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_dec_ref_known(v___x_1074_, 1);
goto v___jp_970_;
}
else
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref_known(v___x_1070_, 2);
v_a_1075_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1071_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v_a_1083_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_999_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_999_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_986_);
lean_dec_ref(v_e_955_);
v_a_1092_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_989_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_989_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
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
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_e_955_);
v_a_1100_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_973_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_973_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_967_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_box(0);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec(v_a_1109_);
return v_res_1120_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1128_ = l_Lean_mkConst(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1137_ = l_Lean_mkConst(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = l_Lean_Expr_cleanupAnnotations(v_e_1138_);
v___x_1157_ = l_Lean_Expr_isApp(v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec_ref(v___x_1156_);
lean_dec_ref(v_e_1138_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1156_);
v___x_1159_ = l_Lean_Expr_isApp(v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v___x_1158_);
lean_dec_ref(v___x_1156_);
lean_dec_ref(v_e_1138_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1158_);
v___x_1161_ = l_Lean_Expr_isApp(v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v___x_1156_);
lean_dec_ref(v_e_1138_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1160_);
v___x_1163_ = l_Lean_Expr_isApp(v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v___x_1156_);
lean_dec_ref(v_e_1138_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1166_ = l_Lean_Expr_isConstOf(v___x_1164_, v___x_1165_);
lean_dec_ref(v___x_1164_);
if (v___x_1166_ == 0)
{
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v___x_1156_);
lean_dec_ref(v_e_1138_);
goto v___jp_1150_;
}
else
{
lean_object* v_arg_1167_; lean_object* v_arg_1168_; lean_object* v_arg_1169_; lean_object* v___x_1170_; 
v_arg_1167_ = lean_ctor_get(v___x_1156_, 1);
lean_inc_ref(v_arg_1167_);
lean_dec_ref(v___x_1156_);
v_arg_1168_ = lean_ctor_get(v___x_1158_, 1);
lean_inc_ref(v_arg_1168_);
lean_dec_ref(v___x_1158_);
v_arg_1169_ = lean_ctor_get(v___x_1160_, 1);
lean_inc_ref(v_arg_1169_);
lean_dec_ref(v___x_1160_);
v___x_1170_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1169_, v_a_1146_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1303_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1303_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1303_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v___x_1176_ = lean_box(0);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v___x_1180_; 
lean_del_object(v___x_1173_);
v___x_1180_ = l_Lean_Meta_getNatValue_x3f(v_arg_1168_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
if (lean_obj_tag(v_a_1181_) == 1)
{
lean_object* v_val_1182_; lean_object* v___x_1183_; 
v_val_1182_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_val_1182_);
lean_dec_ref_known(v_a_1181_, 1);
lean_inc_ref(v_e_1138_);
v___x_1183_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1138_, v_a_1139_, v_a_1143_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; uint8_t v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_unbox(v_a_1184_);
lean_dec(v_a_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec(v_val_1182_);
lean_inc_ref(v_e_1138_);
v___x_1186_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1138_, v_a_1139_, v_a_1143_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1211_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v___x_1192_ = lean_box(0);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
else
{
lean_object* v___x_1196_; 
lean_del_object(v___x_1189_);
lean_inc_ref(v_e_1138_);
v___x_1196_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1199_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1138_, v_a_1197_);
v___x_1200_ = l_Lean_mkApp3(v___x_1198_, v_arg_1168_, v_arg_1167_, v___x_1199_);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = l_Lean_Meta_Grind_pushNewFact(v___x_1200_, v___x_1201_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
return v___x_1202_;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1203_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1196_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1196_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1212_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1186_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1186_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v___x_1220_; 
lean_inc_ref(v_arg_1168_);
v___x_1220_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1168_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_fst_1222_; lean_object* v_snd_1223_; lean_object* v___x_1224_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v_fst_1222_ = lean_ctor_get(v_a_1221_, 0);
lean_inc(v_fst_1222_);
v_snd_1223_ = lean_ctor_get(v_a_1221_, 1);
lean_inc(v_snd_1223_);
lean_dec(v_a_1221_);
lean_inc_ref(v_arg_1167_);
v___x_1224_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1167_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_fst_1226_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v_a_1225_, 1);
lean_inc(v_snd_1227_);
lean_dec(v_a_1225_);
v___x_1228_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
lean_inc(v_fst_1226_);
v___x_1230_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1226_, v_a_1229_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Int_Internal_Linear_Expr_norm(v_a_1231_);
v___x_1233_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1234_ = l_Lean_mkApp6(v___x_1233_, v_arg_1168_, v_arg_1167_, v_fst_1222_, v_fst_1226_, v_snd_1223_, v_snd_1227_);
lean_inc(v_val_1182_);
v___x_1235_ = lean_nat_to_int(v_val_1182_);
v___x_1236_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1236_, 0, v_e_1138_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
lean_ctor_set(v___x_1236_, 2, v_val_1182_);
lean_ctor_set(v___x_1236_, 3, v_a_1231_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1235_);
lean_ctor_set(v___x_1238_, 1, v___x_1232_);
lean_ctor_set(v___x_1238_, 2, v___x_1236_);
lean_ctor_set(v___x_1238_, 3, v___x_1237_);
v___x_1239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1238_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
return v___x_1239_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_snd_1227_);
lean_dec(v_fst_1226_);
lean_dec(v_snd_1223_);
lean_dec(v_fst_1222_);
lean_dec(v_val_1182_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1240_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1230_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_snd_1227_);
lean_dec(v_fst_1226_);
lean_dec(v_snd_1223_);
lean_dec(v_fst_1222_);
lean_dec(v_val_1182_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1248_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1228_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1228_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_snd_1223_);
lean_dec(v_fst_1222_);
lean_dec(v_val_1182_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1256_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1224_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1224_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_val_1182_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1264_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1220_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1220_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_val_1182_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1272_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1183_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1183_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec(v_a_1181_);
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
v___x_1280_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1281_ = l_Lean_indentExpr(v_e_1138_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1143_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v_verbose_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_verbose_1285_ = lean_ctor_get_uint8(v_a_1284_, 0);
lean_dec(v_a_1284_);
if (v_verbose_1285_ == 0)
{
lean_dec_ref_known(v___x_1282_, 2);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Meta_Sym_reportIssue(v___x_1282_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref_known(v___x_1286_, 1);
goto v___jp_1153_;
}
else
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref_known(v___x_1282_, 2);
v_a_1287_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1283_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1295_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1180_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1180_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_arg_1168_);
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_e_1138_);
v_a_1304_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1170_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1170_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec(v_a_1313_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1330_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1378_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
uint8_t v_lia_1347_; 
v_lia_1347_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*17 + 24);
lean_dec(v_a_1343_);
if (v_lia_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_dec_ref(v_e_1327_);
v___x_1348_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v___x_1352_; 
lean_del_object(v___x_1345_);
lean_inc_ref(v_e_1327_);
v___x_1352_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1327_, v_a_1335_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_Expr_cleanupAnnotations(v_a_1353_);
lean_dec(v_a_1353_);
v___x_1355_ = l_Lean_Expr_isApp(v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec_ref(v_e_1327_);
goto v___jp_1339_;
}
else
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1357_ = l_Lean_Expr_isApp(v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec_ref(v___x_1356_);
lean_dec_ref(v_e_1327_);
goto v___jp_1339_;
}
else
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1356_);
lean_dec_ref(v___x_1356_);
v___x_1359_ = l_Lean_Expr_isApp(v___x_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___x_1358_);
lean_dec_ref(v_e_1327_);
goto v___jp_1339_;
}
else
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1361_ = l_Lean_Expr_isApp(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_e_1327_);
goto v___jp_1339_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1360_);
v___x_1363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1364_ = l_Lean_Expr_isConstOf(v___x_1362_, v___x_1363_);
lean_dec_ref(v___x_1362_);
if (v___x_1364_ == 0)
{
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_e_1327_);
goto v___jp_1339_;
}
else
{
lean_object* v_arg_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_arg_1365_ = lean_ctor_get(v___x_1360_, 1);
lean_inc_ref(v_arg_1365_);
lean_dec_ref(v___x_1360_);
v___x_1366_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1367_ = l_Lean_Expr_isConstOf(v_arg_1365_, v___x_1366_);
lean_dec_ref(v_arg_1365_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
return v___x_1369_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_e_1327_);
v_a_1370_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1352_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1352_);
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
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v_e_1327_);
v_a_1379_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1342_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1342_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec(v_a_1388_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1402_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1403_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1401_, v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1405_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
}
#ifdef __cplusplus
}
#endif
