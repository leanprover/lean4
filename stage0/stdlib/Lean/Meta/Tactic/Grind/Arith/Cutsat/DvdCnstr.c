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
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* v_d_6_; lean_object* v_p_7_; lean_object* v_d_8_; lean_object* v___y_10_; lean_object* v___y_11_; lean_object* v___x_16_; lean_object* v___y_18_; uint8_t v___x_22_; 
v_d_6_ = lean_ctor_get(v_c_5_, 0);
v_p_7_ = lean_ctor_get(v_c_5_, 1);
v_d_8_ = lean_nat_abs(v_d_6_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_dec_le(v_d_8_, v___x_16_);
if (v___x_22_ == 0)
{
if (lean_obj_tag(v_p_7_) == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___y_18_ = v___x_23_;
goto v___jp_17_;
}
else
{
lean_object* v_k_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_k_24_ = lean_ctor_get(v_p_7_, 0);
v___x_25_ = lean_nat_abs(v_k_24_);
v___x_26_ = lean_nat_dec_eq(v___x_25_, v___x_16_);
lean_dec(v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_snd_29_; lean_object* v_fst_30_; lean_object* v_fst_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_d_8_);
v___x_27_ = lean_nat_to_int(v_d_8_);
v___x_28_ = l_Lean_Meta_Grind_Arith_gcdExt(v_k_24_, v___x_27_);
lean_dec(v___x_27_);
v_snd_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_snd_29_);
v_fst_30_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_fst_30_);
lean_dec_ref(v___x_28_);
v_fst_31_ = lean_ctor_get(v_snd_29_, 0);
lean_inc(v_fst_31_);
lean_dec(v_snd_29_);
v___x_32_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_33_ = lean_int_dec_eq(v_fst_30_, v___x_32_);
lean_dec(v_fst_30_);
if (v___x_33_ == 0)
{
lean_dec(v_fst_31_);
v___y_18_ = v___x_32_;
goto v___jp_17_;
}
else
{
v___y_18_ = v_fst_31_;
goto v___jp_17_;
}
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___y_18_ = v___x_34_;
goto v___jp_17_;
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
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_d_6_);
v___x_14_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_14_, 0, v_c_5_);
lean_ctor_set(v___x_14_, 1, v___y_10_);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v_d_6_);
lean_ctor_set(v___x_15_, 1, v_p_12_);
lean_ctor_set(v___x_15_, 2, v___x_14_);
return v___x_15_;
}
else
{
lean_dec_ref(v_p_12_);
lean_dec(v___y_10_);
return v_c_5_;
}
}
v___jp_17_:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_20_ = lean_int_dec_eq(v___y_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_inc_ref(v_p_7_);
v___x_21_ = l_Int_Internal_Linear_Poly_mul(v_p_7_, v___y_18_);
v___y_10_ = v___y_18_;
v___y_11_ = v___x_21_;
goto v___jp_9_;
}
else
{
lean_inc_ref(v_p_7_);
v___y_10_ = v___y_18_;
v___y_11_ = v_p_7_;
goto v___jp_9_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* v_c_37_){
_start:
{
lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_57_; lean_object* v_d_58_; lean_object* v_p_59_; lean_object* v_d_64_; lean_object* v_p_65_; uint8_t v___x_66_; 
v_d_64_ = lean_ctor_get(v_c_37_, 0);
lean_inc(v_d_64_);
v_p_65_ = lean_ctor_get(v_c_37_, 1);
v___x_66_ = l_Int_Internal_Linear_Poly_isSorted(v_p_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc_ref(v_p_65_);
v___x_67_ = l_Int_Internal_Linear_Poly_norm(v_p_65_);
v___x_68_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_68_, 0, v_c_37_);
lean_inc_ref(v___x_67_);
lean_inc(v_d_64_);
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_d_64_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_68_);
v___y_57_ = v___x_69_;
v_d_58_ = v_d_64_;
v_p_59_ = v___x_67_;
goto v___jp_56_;
}
else
{
lean_inc_ref(v_p_65_);
v___y_57_ = v_c_37_;
v_d_58_ = v_d_64_;
v_p_59_ = v_p_65_;
goto v___jp_56_;
}
v___jp_38_:
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = l_Int_Internal_Linear_Poly_getConst(v___y_42_);
v___x_45_ = lean_int_emod(v___x_44_, v___y_43_);
lean_dec(v___x_44_);
v___x_46_ = lean_int_dec_eq(v___x_45_, v___y_41_);
lean_dec(v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_40_);
v___x_47_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_39_);
return v___x_47_;
}
else
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs___closed__0);
v___x_49_ = lean_int_dec_eq(v___y_43_, v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = lean_int_ediv(v___y_40_, v___y_43_);
lean_dec(v___y_40_);
v___x_51_ = l_Int_Internal_Linear_Poly_div(v___y_43_, v___y_42_);
lean_dec(v___y_43_);
v___x_52_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_52_, 0, v___y_39_);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
v___x_54_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___x_53_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; 
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_40_);
v___x_55_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_39_);
return v___x_55_;
}
}
}
v___jp_56_:
{
lean_object* v_g_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
lean_inc(v_d_58_);
v_g_60_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_59_, v_d_58_);
v___x_61_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_62_ = lean_int_dec_lt(v_d_58_, v___x_61_);
if (v___x_62_ == 0)
{
v___y_39_ = v___y_57_;
v___y_40_ = v_d_58_;
v___y_41_ = v___x_61_;
v___y_42_ = v_p_59_;
v___y_43_ = v_g_60_;
goto v___jp_38_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = lean_int_neg(v_g_60_);
lean_dec(v_g_60_);
v___y_39_ = v___y_57_;
v___y_40_ = v_d_58_;
v___y_41_ = v___x_61_;
v___y_42_ = v_p_59_;
v___y_43_ = v___x_63_;
goto v___jp_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_env_77_; uint8_t v___x_78_; lean_object* v_env_79_; lean_object* v___x_80_; lean_object* v_toCold_81_; lean_object* v_mctx_82_; lean_object* v_lctx_83_; lean_object* v_options_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_76_ = lean_st_ref_get(v___y_74_);
v_env_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_env_77_);
lean_dec(v___x_76_);
v___x_78_ = 0;
v_env_79_ = l_Lean_Environment_setRecordingDeps(v_env_77_, v___x_78_);
v___x_80_ = lean_st_ref_get(v___y_72_);
v_toCold_81_ = lean_ctor_get(v___y_73_, 0);
v_mctx_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc_ref(v_mctx_82_);
lean_dec(v___x_80_);
v_lctx_83_ = lean_ctor_get(v___y_71_, 2);
v_options_84_ = lean_ctor_get(v_toCold_81_, 2);
lean_inc_ref(v_options_84_);
lean_inc_ref(v_lctx_83_);
v___x_85_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_85_, 0, v_env_79_);
lean_ctor_set(v___x_85_, 1, v_mctx_82_);
lean_ctor_set(v___x_85_, 2, v_lctx_83_);
lean_ctor_set(v___x_85_, 3, v_options_84_);
v___x_86_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_msgData_70_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_94_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_95_; double v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_float_of_nat(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_100_, lean_object* v_msg_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_ref_107_; lean_object* v___x_108_; lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_154_; 
v_ref_107_ = lean_ctor_get(v___y_104_, 2);
v___x_108_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_154_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_154_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_154_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v_traceState_114_; lean_object* v_env_115_; lean_object* v_nextMacroScope_116_; lean_object* v_ngen_117_; lean_object* v_auxDeclNGen_118_; lean_object* v_cache_119_; lean_object* v_recordedDeps_120_; lean_object* v_messages_121_; lean_object* v_infoState_122_; lean_object* v_snapshotTasks_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_153_; 
v___x_113_ = lean_st_ref_take(v___y_105_);
v_traceState_114_ = lean_ctor_get(v___x_113_, 4);
v_env_115_ = lean_ctor_get(v___x_113_, 0);
v_nextMacroScope_116_ = lean_ctor_get(v___x_113_, 1);
v_ngen_117_ = lean_ctor_get(v___x_113_, 2);
v_auxDeclNGen_118_ = lean_ctor_get(v___x_113_, 3);
v_cache_119_ = lean_ctor_get(v___x_113_, 5);
v_recordedDeps_120_ = lean_ctor_get(v___x_113_, 6);
v_messages_121_ = lean_ctor_get(v___x_113_, 7);
v_infoState_122_ = lean_ctor_get(v___x_113_, 8);
v_snapshotTasks_123_ = lean_ctor_get(v___x_113_, 9);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_153_ == 0)
{
v___x_125_ = v___x_113_;
v_isShared_126_ = v_isSharedCheck_153_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snapshotTasks_123_);
lean_inc(v_infoState_122_);
lean_inc(v_messages_121_);
lean_inc(v_recordedDeps_120_);
lean_inc(v_cache_119_);
lean_inc(v_traceState_114_);
lean_inc(v_auxDeclNGen_118_);
lean_inc(v_ngen_117_);
lean_inc(v_nextMacroScope_116_);
lean_inc(v_env_115_);
lean_dec(v___x_113_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_153_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint64_t v_tid_127_; lean_object* v_traces_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_152_; 
v_tid_127_ = lean_ctor_get_uint64(v_traceState_114_, sizeof(void*)*1);
v_traces_128_ = lean_ctor_get(v_traceState_114_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_traceState_114_);
if (v_isSharedCheck_152_ == 0)
{
v___x_130_ = v_traceState_114_;
v_isShared_131_ = v_isSharedCheck_152_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_traces_128_);
lean_dec(v_traceState_114_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_152_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; double v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_132_ = lean_box(0);
v___x_133_ = lean_box(0);
v___x_134_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_135_ = 0;
v___x_136_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_137_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_137_, 0, v_cls_100_);
lean_ctor_set(v___x_137_, 1, v___x_133_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
lean_ctor_set_float(v___x_137_, sizeof(void*)*3, v___x_134_);
lean_ctor_set_float(v___x_137_, sizeof(void*)*3 + 8, v___x_134_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*3 + 16, v___x_135_);
v___x_138_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_139_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v_a_109_);
lean_ctor_set(v___x_139_, 2, v___x_138_);
lean_inc(v_ref_107_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_ref_107_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = l_Lean_PersistentArray_push___redArg(v_traces_128_, v___x_140_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_141_);
v___x_143_ = v___x_130_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_141_);
lean_ctor_set_uint64(v_reuseFailAlloc_151_, sizeof(void*)*1, v_tid_127_);
v___x_143_ = v_reuseFailAlloc_151_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v___x_143_);
v___x_145_ = v___x_125_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_env_115_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_nextMacroScope_116_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_ngen_117_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_auxDeclNGen_118_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_150_, 5, v_cache_119_);
lean_ctor_set(v_reuseFailAlloc_150_, 6, v_recordedDeps_120_);
lean_ctor_set(v_reuseFailAlloc_150_, 7, v_messages_121_);
lean_ctor_set(v_reuseFailAlloc_150_, 8, v_infoState_122_);
lean_ctor_set(v_reuseFailAlloc_150_, 9, v_snapshotTasks_123_);
v___x_145_ = v_reuseFailAlloc_150_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_st_ref_put(v___y_105_, v___x_145_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_132_);
v___x_148_ = v___x_111_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_132_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_155_, lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_155_, v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_cls_175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_177_ = l_Lean_Name_append(v___x_176_, v_cls_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_181_, lean_object* v_x_182_, lean_object* v_c_u2081_183_, lean_object* v_b_184_, lean_object* v_c_u2082_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_toCold_197_; lean_object* v_options_198_; lean_object* v_p_199_; lean_object* v_d_200_; lean_object* v_p_201_; lean_object* v_inheritedTraceOptions_202_; uint8_t v_hasTrace_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_d_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_p_210_; 
v_toCold_197_ = lean_ctor_get(v_a_194_, 0);
v_options_198_ = lean_ctor_get(v_toCold_197_, 2);
v_p_199_ = lean_ctor_get(v_c_u2081_183_, 0);
v_d_200_ = lean_ctor_get(v_c_u2082_185_, 0);
v_p_201_ = lean_ctor_get(v_c_u2082_185_, 1);
v_inheritedTraceOptions_202_ = lean_ctor_get(v_toCold_197_, 11);
v_hasTrace_203_ = lean_ctor_get_uint8(v_options_198_, sizeof(void*)*1);
v___x_204_ = lean_int_mul(v_a_181_, v_d_200_);
v___x_205_ = lean_nat_abs(v___x_204_);
lean_dec(v___x_204_);
v_d_206_ = lean_nat_to_int(v___x_205_);
lean_inc_ref(v_p_201_);
v___x_207_ = l_Int_Internal_Linear_Poly_mul(v_p_201_, v_a_181_);
v___x_208_ = lean_int_neg(v_b_184_);
lean_inc_ref(v_p_199_);
v___x_209_ = l_Int_Internal_Linear_Poly_mul(v_p_199_, v___x_208_);
lean_dec(v___x_208_);
v_p_210_ = l_Int_Internal_Linear_Poly_combine(v___x_207_, v___x_209_);
if (v_hasTrace_203_ == 0)
{
goto v___jp_211_;
}
else
{
lean_object* v_cls_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_cls_215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_216_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_217_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_202_, v_options_198_, v___x_216_);
if (v___x_217_ == 0)
{
goto v___jp_211_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_182_, v_a_186_, v_a_194_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
lean_inc_ref(v_c_u2081_183_);
v___x_220_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_183_, v_a_186_, v_a_194_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
lean_inc_ref(v_c_u2082_185_);
v___x_222_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_185_, v_a_186_, v_a_194_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_Lean_MessageData_ofExpr(v_a_219_);
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_221_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_225_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_223_);
v___x_230_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_215_, v___x_229_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec_ref_known(v___x_230_, 1);
goto v___jp_211_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_p_210_);
lean_dec(v_d_206_);
lean_dec_ref(v_c_u2082_185_);
lean_dec_ref(v_c_u2081_183_);
lean_dec(v_x_182_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec_ref(v_p_210_);
lean_dec(v_d_206_);
lean_dec_ref(v_c_u2082_185_);
lean_dec_ref(v_c_u2081_183_);
lean_dec(v_x_182_);
v_a_239_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_222_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_222_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v_a_219_);
lean_dec_ref(v_p_210_);
lean_dec(v_d_206_);
lean_dec_ref(v_c_u2082_185_);
lean_dec_ref(v_c_u2081_183_);
lean_dec(v_x_182_);
v_a_247_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_220_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_220_);
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
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_p_210_);
lean_dec(v_d_206_);
lean_dec_ref(v_c_u2082_185_);
lean_dec_ref(v_c_u2081_183_);
lean_dec(v_x_182_);
v_a_255_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_218_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_218_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
v___jp_211_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_212_, 0, v_x_182_);
lean_ctor_set(v___x_212_, 1, v_c_u2081_183_);
lean_ctor_set(v___x_212_, 2, v_c_u2082_185_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v_d_206_);
lean_ctor_set(v___x_213_, 1, v_p_210_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_263_, lean_object* v_x_264_, lean_object* v_c_u2081_265_, lean_object* v_b_266_, lean_object* v_c_u2082_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_263_, v_x_264_, v_c_u2081_265_, v_b_266_, v_c_u2082_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec(v_a_268_);
lean_dec(v_b_266_);
lean_dec(v_a_263_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_280_, v_msg_281_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_294_, lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_294_, v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec(v___y_296_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l_Lean_maxRecDepthErrorMessage;
v___x_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_316_ = l_Lean_MessageData_ofFormat(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_318_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_319_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_320_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_328_, lean_object* v_ref_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_329_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_342_, lean_object* v_ref_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_342_, v_ref_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_p_368_; lean_object* v_toCold_369_; lean_object* v_currRecDepth_370_; lean_object* v_ref_371_; uint16_t v_optionFlags_372_; uint8_t v_suppressElabErrors_373_; uint8_t v_isRecordingDeps_374_; lean_object* v_maxRecDepth_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_p_368_ = lean_ctor_get(v_c_356_, 1);
v_toCold_369_ = lean_ctor_get(v_a_365_, 0);
lean_inc_ref(v_toCold_369_);
v_currRecDepth_370_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_currRecDepth_370_);
v_ref_371_ = lean_ctor_get(v_a_365_, 2);
lean_inc(v_ref_371_);
v_optionFlags_372_ = lean_ctor_get_uint16(v_a_365_, sizeof(void*)*3);
v_suppressElabErrors_373_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*3 + 2);
v_isRecordingDeps_374_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_365_);
v_maxRecDepth_406_ = lean_ctor_get(v_toCold_369_, 3);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_dec_eq(v_maxRecDepth_406_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_eq(v_currRecDepth_370_, v_maxRecDepth_406_);
if (v___x_409_ == 0)
{
goto v___jp_375_;
}
else
{
lean_object* v___x_410_; 
lean_dec(v_currRecDepth_370_);
lean_dec_ref(v_toCold_369_);
lean_dec_ref(v_c_356_);
v___x_410_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_371_);
return v___x_410_;
}
}
else
{
goto v___jp_375_;
}
v___jp_375_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_currRecDepth_370_, v___x_376_);
lean_dec(v_currRecDepth_370_);
v___x_378_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_378_, 0, v_toCold_369_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set(v___x_378_, 2, v_ref_371_);
lean_ctor_set_uint16(v___x_378_, sizeof(void*)*3, v_optionFlags_372_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*3 + 2, v_suppressElabErrors_373_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*3 + 3, v_isRecordingDeps_374_);
lean_inc_ref(v_p_368_);
v___x_379_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_368_, v_a_357_, v___x_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_397_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_a_380_) == 1)
{
lean_object* v_val_384_; lean_object* v_snd_385_; lean_object* v_snd_386_; lean_object* v_fst_387_; lean_object* v_fst_388_; lean_object* v_p_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_del_object(v___x_382_);
v_val_384_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_a_380_, 1);
v_snd_385_ = lean_ctor_get(v_val_384_, 1);
lean_inc(v_snd_385_);
v_snd_386_ = lean_ctor_get(v_snd_385_, 1);
lean_inc(v_snd_386_);
v_fst_387_ = lean_ctor_get(v_val_384_, 0);
lean_inc(v_fst_387_);
lean_dec(v_val_384_);
v_fst_388_ = lean_ctor_get(v_snd_385_, 0);
lean_inc(v_fst_388_);
lean_dec(v_snd_385_);
v_p_389_ = lean_ctor_get(v_snd_386_, 0);
v___x_390_ = l_Int_Internal_Linear_Poly_coeff(v_p_389_, v_fst_388_);
v___x_391_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_390_, v_fst_388_, v_snd_386_, v_fst_387_, v_c_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v___x_378_, v_a_366_);
lean_dec(v_fst_387_);
lean_dec(v___x_390_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v_c_356_ = v_a_392_;
v_a_365_ = v___x_378_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_378_, 3);
return v___x_391_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec(v_a_380_);
lean_dec_ref_known(v___x_378_, 3);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_c_356_);
v___x_395_ = v___x_382_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_c_356_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref_known(v___x_378_, 3);
lean_dec_ref(v_c_356_);
v_a_398_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_379_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_379_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec(v_a_412_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v___x_424_, lean_object* v_v_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_vars_427_; lean_object* v_varMap_428_; lean_object* v_varsHistory_429_; lean_object* v_natToIntMap_430_; lean_object* v_natDef_431_; lean_object* v_dvds_432_; lean_object* v_lowers_433_; lean_object* v_uppers_434_; lean_object* v_diseqs_435_; lean_object* v_elimEqs_436_; lean_object* v_elimStack_437_; lean_object* v_occurs_438_; lean_object* v_assignment_439_; lean_object* v_nextCnstrId_440_; uint8_t v_caseSplits_441_; lean_object* v_steps_442_; lean_object* v_penalties_443_; lean_object* v_numReorderRequests_444_; lean_object* v_conflict_x3f_445_; lean_object* v_diseqSplits_446_; lean_object* v_divMod_447_; uint8_t v_usedCommRing_448_; lean_object* v_nonlinearOccs_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_458_; 
v_vars_427_ = lean_ctor_get(v_s_426_, 0);
v_varMap_428_ = lean_ctor_get(v_s_426_, 1);
v_varsHistory_429_ = lean_ctor_get(v_s_426_, 2);
v_natToIntMap_430_ = lean_ctor_get(v_s_426_, 3);
v_natDef_431_ = lean_ctor_get(v_s_426_, 4);
v_dvds_432_ = lean_ctor_get(v_s_426_, 5);
v_lowers_433_ = lean_ctor_get(v_s_426_, 6);
v_uppers_434_ = lean_ctor_get(v_s_426_, 7);
v_diseqs_435_ = lean_ctor_get(v_s_426_, 8);
v_elimEqs_436_ = lean_ctor_get(v_s_426_, 9);
v_elimStack_437_ = lean_ctor_get(v_s_426_, 10);
v_occurs_438_ = lean_ctor_get(v_s_426_, 11);
v_assignment_439_ = lean_ctor_get(v_s_426_, 12);
v_nextCnstrId_440_ = lean_ctor_get(v_s_426_, 13);
v_caseSplits_441_ = lean_ctor_get_uint8(v_s_426_, sizeof(void*)*21);
v_steps_442_ = lean_ctor_get(v_s_426_, 14);
v_penalties_443_ = lean_ctor_get(v_s_426_, 15);
v_numReorderRequests_444_ = lean_ctor_get(v_s_426_, 16);
v_conflict_x3f_445_ = lean_ctor_get(v_s_426_, 17);
v_diseqSplits_446_ = lean_ctor_get(v_s_426_, 18);
v_divMod_447_ = lean_ctor_get(v_s_426_, 19);
v_usedCommRing_448_ = lean_ctor_get_uint8(v_s_426_, sizeof(void*)*21 + 1);
v_nonlinearOccs_449_ = lean_ctor_get(v_s_426_, 20);
v_isSharedCheck_458_ = !lean_is_exclusive(v_s_426_);
if (v_isSharedCheck_458_ == 0)
{
v___x_451_ = v_s_426_;
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_nonlinearOccs_449_);
lean_inc(v_divMod_447_);
lean_inc(v_diseqSplits_446_);
lean_inc(v_conflict_x3f_445_);
lean_inc(v_numReorderRequests_444_);
lean_inc(v_penalties_443_);
lean_inc(v_steps_442_);
lean_inc(v_nextCnstrId_440_);
lean_inc(v_assignment_439_);
lean_inc(v_occurs_438_);
lean_inc(v_elimStack_437_);
lean_inc(v_elimEqs_436_);
lean_inc(v_diseqs_435_);
lean_inc(v_uppers_434_);
lean_inc(v_lowers_433_);
lean_inc(v_dvds_432_);
lean_inc(v_natDef_431_);
lean_inc(v_natToIntMap_430_);
lean_inc(v_varsHistory_429_);
lean_inc(v_varMap_428_);
lean_inc(v_vars_427_);
lean_dec(v_s_426_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_424_);
v___x_454_ = l_Lean_PersistentArray_set___redArg(v_dvds_432_, v_v_425_, v___x_453_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 5, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_vars_427_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_varMap_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_varsHistory_429_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_natToIntMap_430_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_natDef_431_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_lowers_433_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_uppers_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_diseqs_435_);
lean_ctor_set(v_reuseFailAlloc_457_, 9, v_elimEqs_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 10, v_elimStack_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 11, v_occurs_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 12, v_assignment_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 13, v_nextCnstrId_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 14, v_steps_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 15, v_penalties_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 16, v_numReorderRequests_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 17, v_conflict_x3f_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 18, v_diseqSplits_446_);
lean_ctor_set(v_reuseFailAlloc_457_, 19, v_divMod_447_);
lean_ctor_set(v_reuseFailAlloc_457_, 20, v_nonlinearOccs_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*21, v_caseSplits_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*21 + 1, v_usedCommRing_448_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v___x_459_, lean_object* v_v_460_, lean_object* v_s_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v___x_459_, v_v_460_, v_s_461_);
lean_dec(v_v_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_463_, lean_object* v_s_464_){
_start:
{
lean_object* v_vars_465_; lean_object* v_varMap_466_; lean_object* v_varsHistory_467_; lean_object* v_natToIntMap_468_; lean_object* v_natDef_469_; lean_object* v_dvds_470_; lean_object* v_lowers_471_; lean_object* v_uppers_472_; lean_object* v_diseqs_473_; lean_object* v_elimEqs_474_; lean_object* v_elimStack_475_; lean_object* v_occurs_476_; lean_object* v_assignment_477_; lean_object* v_nextCnstrId_478_; uint8_t v_caseSplits_479_; lean_object* v_steps_480_; lean_object* v_penalties_481_; lean_object* v_numReorderRequests_482_; lean_object* v_conflict_x3f_483_; lean_object* v_diseqSplits_484_; lean_object* v_divMod_485_; uint8_t v_usedCommRing_486_; lean_object* v_nonlinearOccs_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_496_; 
v_vars_465_ = lean_ctor_get(v_s_464_, 0);
v_varMap_466_ = lean_ctor_get(v_s_464_, 1);
v_varsHistory_467_ = lean_ctor_get(v_s_464_, 2);
v_natToIntMap_468_ = lean_ctor_get(v_s_464_, 3);
v_natDef_469_ = lean_ctor_get(v_s_464_, 4);
v_dvds_470_ = lean_ctor_get(v_s_464_, 5);
v_lowers_471_ = lean_ctor_get(v_s_464_, 6);
v_uppers_472_ = lean_ctor_get(v_s_464_, 7);
v_diseqs_473_ = lean_ctor_get(v_s_464_, 8);
v_elimEqs_474_ = lean_ctor_get(v_s_464_, 9);
v_elimStack_475_ = lean_ctor_get(v_s_464_, 10);
v_occurs_476_ = lean_ctor_get(v_s_464_, 11);
v_assignment_477_ = lean_ctor_get(v_s_464_, 12);
v_nextCnstrId_478_ = lean_ctor_get(v_s_464_, 13);
v_caseSplits_479_ = lean_ctor_get_uint8(v_s_464_, sizeof(void*)*21);
v_steps_480_ = lean_ctor_get(v_s_464_, 14);
v_penalties_481_ = lean_ctor_get(v_s_464_, 15);
v_numReorderRequests_482_ = lean_ctor_get(v_s_464_, 16);
v_conflict_x3f_483_ = lean_ctor_get(v_s_464_, 17);
v_diseqSplits_484_ = lean_ctor_get(v_s_464_, 18);
v_divMod_485_ = lean_ctor_get(v_s_464_, 19);
v_usedCommRing_486_ = lean_ctor_get_uint8(v_s_464_, sizeof(void*)*21 + 1);
v_nonlinearOccs_487_ = lean_ctor_get(v_s_464_, 20);
v_isSharedCheck_496_ = !lean_is_exclusive(v_s_464_);
if (v_isSharedCheck_496_ == 0)
{
v___x_489_ = v_s_464_;
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_nonlinearOccs_487_);
lean_inc(v_divMod_485_);
lean_inc(v_diseqSplits_484_);
lean_inc(v_conflict_x3f_483_);
lean_inc(v_numReorderRequests_482_);
lean_inc(v_penalties_481_);
lean_inc(v_steps_480_);
lean_inc(v_nextCnstrId_478_);
lean_inc(v_assignment_477_);
lean_inc(v_occurs_476_);
lean_inc(v_elimStack_475_);
lean_inc(v_elimEqs_474_);
lean_inc(v_diseqs_473_);
lean_inc(v_uppers_472_);
lean_inc(v_lowers_471_);
lean_inc(v_dvds_470_);
lean_inc(v_natDef_469_);
lean_inc(v_natToIntMap_468_);
lean_inc(v_varsHistory_467_);
lean_inc(v_varMap_466_);
lean_inc(v_vars_465_);
lean_dec(v_s_464_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_491_ = lean_box(0);
v___x_492_ = l_Lean_PersistentArray_set___redArg(v_dvds_470_, v_v_463_, v___x_491_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 5, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_vars_465_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_varMap_466_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_varsHistory_467_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_natToIntMap_468_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_natDef_469_);
lean_ctor_set(v_reuseFailAlloc_495_, 5, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 6, v_lowers_471_);
lean_ctor_set(v_reuseFailAlloc_495_, 7, v_uppers_472_);
lean_ctor_set(v_reuseFailAlloc_495_, 8, v_diseqs_473_);
lean_ctor_set(v_reuseFailAlloc_495_, 9, v_elimEqs_474_);
lean_ctor_set(v_reuseFailAlloc_495_, 10, v_elimStack_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 11, v_occurs_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 12, v_assignment_477_);
lean_ctor_set(v_reuseFailAlloc_495_, 13, v_nextCnstrId_478_);
lean_ctor_set(v_reuseFailAlloc_495_, 14, v_steps_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 15, v_penalties_481_);
lean_ctor_set(v_reuseFailAlloc_495_, 16, v_numReorderRequests_482_);
lean_ctor_set(v_reuseFailAlloc_495_, 17, v_conflict_x3f_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 18, v_diseqSplits_484_);
lean_ctor_set(v_reuseFailAlloc_495_, 19, v_divMod_485_);
lean_ctor_set(v_reuseFailAlloc_495_, 20, v_nonlinearOccs_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*21, v_caseSplits_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*21 + 1, v_usedCommRing_486_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_497_, lean_object* v_s_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_497_, v_s_498_);
lean_dec(v_v_497_);
return v_res_499_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_509_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_510_ = l_Lean_Name_append(v___x_509_, v___x_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v_toCold_663_; lean_object* v_currRecDepth_664_; lean_object* v_ref_665_; uint16_t v_optionFlags_666_; uint8_t v_suppressElabErrors_667_; uint8_t v_isRecordingDeps_668_; lean_object* v_options_669_; lean_object* v_maxRecDepth_670_; lean_object* v_inheritedTraceOptions_671_; lean_object* v___x_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_toCold_663_ = lean_ctor_get(v_a_520_, 0);
lean_inc_ref(v_toCold_663_);
v_currRecDepth_664_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_currRecDepth_664_);
v_ref_665_ = lean_ctor_get(v_a_520_, 2);
lean_inc(v_ref_665_);
v_optionFlags_666_ = lean_ctor_get_uint16(v_a_520_, sizeof(void*)*3);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v_a_520_, sizeof(void*)*3 + 2);
v_isRecordingDeps_668_ = lean_ctor_get_uint8(v_a_520_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_520_);
v_options_669_ = lean_ctor_get(v_toCold_663_, 2);
lean_inc_ref(v_options_669_);
v_maxRecDepth_670_ = lean_ctor_get(v_toCold_663_, 3);
v_inheritedTraceOptions_671_ = lean_ctor_get(v_toCold_663_, 11);
lean_inc_ref(v_inheritedTraceOptions_671_);
v___x_672_ = lean_box(0);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_nat_dec_eq(v_maxRecDepth_670_, v___x_855_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; 
v___x_857_ = lean_nat_dec_eq(v_currRecDepth_664_, v_maxRecDepth_670_);
if (v___x_857_ == 0)
{
goto v___jp_814_;
}
else
{
lean_object* v___x_858_; 
lean_dec_ref(v_inheritedTraceOptions_671_);
lean_dec_ref(v_options_669_);
lean_dec(v_currRecDepth_664_);
lean_dec_ref(v_toCold_663_);
lean_dec_ref(v_c_511_);
v___x_858_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_665_);
return v___x_858_;
}
}
else
{
goto v___jp_814_;
}
v___jp_523_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
v___jp_526_:
{
lean_object* v___x_534_; 
v___x_534_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_527_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec_ref(v___y_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec_ref_known(v___x_534_, 1);
v___x_535_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_536_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_535_, v___y_528_, v___y_529_);
return v___x_536_;
}
else
{
lean_dec_ref(v___y_528_);
return v___x_534_;
}
}
v___jp_537_:
{
if (lean_obj_tag(v___y_559_) == 1)
{
lean_object* v_val_560_; lean_object* v_p_561_; 
lean_dec_ref(v___y_546_);
lean_dec_ref(v___y_541_);
v_val_560_ = lean_ctor_get(v___y_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___y_559_, 1);
v_p_561_ = lean_ctor_get(v_val_560_, 1);
lean_inc_ref(v_p_561_);
if (lean_obj_tag(v_p_561_) == 1)
{
lean_object* v_d_562_; lean_object* v_k_563_; lean_object* v_p_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_617_; 
v_d_562_ = lean_ctor_get(v_val_560_, 0);
v_k_563_ = lean_ctor_get(v_p_561_, 0);
v_p_564_ = lean_ctor_get(v_p_561_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_p_561_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_p_561_, 1);
lean_dec(v_unused_618_);
v___x_566_ = v_p_561_;
v_isShared_567_ = v_isSharedCheck_617_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_p_564_);
lean_inc(v_k_563_);
lean_dec(v_p_561_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_617_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_snd_571_; lean_object* v_fst_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_616_; 
v___x_568_ = lean_int_mul(v___y_542_, v_d_562_);
v___x_569_ = lean_int_mul(v_k_563_, v___y_547_);
v___x_570_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_568_, v___x_569_);
lean_dec(v___x_569_);
lean_dec(v___x_568_);
v_snd_571_ = lean_ctor_get(v___x_570_, 1);
v_fst_572_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_616_ == 0)
{
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_572_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_615_; 
v_fst_576_ = lean_ctor_get(v_snd_571_, 0);
v_snd_577_ = lean_ctor_get(v_snd_571_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_615_ == 0)
{
v___x_579_ = v_snd_571_;
v_isShared_580_ = v_isSharedCheck_615_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v_snd_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_615_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_581_ = lean_int_mul(v_fst_576_, v_d_562_);
lean_dec(v_fst_576_);
lean_inc_ref(v___y_555_);
v___x_582_ = l_Int_Internal_Linear_Poly_mul(v___y_555_, v___x_581_);
lean_dec(v___x_581_);
v___x_583_ = lean_int_mul(v_snd_577_, v___y_547_);
lean_dec(v_snd_577_);
lean_inc_ref(v_p_564_);
v___x_584_ = l_Int_Internal_Linear_Poly_mul(v_p_564_, v___x_583_);
lean_dec(v___x_583_);
v___x_585_ = lean_int_mul(v___y_547_, v_d_562_);
lean_dec(v___y_547_);
v___x_586_ = l_Int_Internal_Linear_Poly_combine(v___x_582_, v___x_584_);
lean_inc(v_fst_572_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 2, v___x_586_);
lean_ctor_set(v___x_566_, 1, v___y_552_);
lean_ctor_set(v___x_566_, 0, v_fst_572_);
v___x_588_ = v___x_566_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_572_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___y_552_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_586_);
v___x_588_ = v_reuseFailAlloc_614_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
lean_inc(v_val_560_);
lean_inc_ref(v___y_556_);
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 5);
lean_ctor_set(v___x_579_, 1, v_val_560_);
lean_ctor_set(v___x_579_, 0, v___y_556_);
v___x_590_ = v___x_579_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_val_560_);
v___x_590_ = v_reuseFailAlloc_613_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_591_, 0, v___x_585_);
lean_ctor_set(v___x_591_, 1, v___x_588_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
v___x_592_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_593_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_592_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; 
lean_dec_ref_known(v___x_593_, 1);
lean_inc_ref(v___y_551_);
v___x_594_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_591_, v___y_554_, v___y_550_, v___y_538_, v___y_540_, v___y_545_, v___y_544_, v___y_548_, v___y_557_, v___y_551_, v___y_558_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_595_ = l_Int_Internal_Linear_Poly_mul(v___y_555_, v_k_563_);
lean_dec(v_k_563_);
v___x_596_ = lean_int_neg(v___y_542_);
lean_dec(v___y_542_);
v___x_597_ = l_Int_Internal_Linear_Poly_mul(v_p_564_, v___x_596_);
lean_dec(v___x_596_);
v___x_598_ = l_Int_Internal_Linear_Poly_combine(v___x_595_, v___x_597_);
lean_inc(v_val_560_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 6);
lean_ctor_set(v___x_574_, 1, v_val_560_);
lean_ctor_set(v___x_574_, 0, v___y_556_);
v___x_600_ = v___x_574_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_val_560_);
v___x_600_ = v_reuseFailAlloc_612_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v_val_560_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; lean_object* v_unused_610_; lean_object* v_unused_611_; 
v_unused_609_ = lean_ctor_get(v_val_560_, 2);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_val_560_, 1);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_val_560_, 0);
lean_dec(v_unused_611_);
v___x_602_ = v_val_560_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_dec(v_val_560_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_598_);
lean_ctor_set(v___x_602_, 0, v_fst_572_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_fst_572_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_600_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_c_511_ = v___x_605_;
v_a_512_ = v___y_554_;
v_a_513_ = v___y_550_;
v_a_514_ = v___y_538_;
v_a_515_ = v___y_540_;
v_a_516_ = v___y_545_;
v_a_517_ = v___y_544_;
v_a_518_ = v___y_548_;
v_a_519_ = v___y_557_;
v_a_520_ = v___y_551_;
v_a_521_ = v___y_558_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
lean_dec_ref(v_p_564_);
lean_dec(v_k_563_);
lean_dec(v_val_560_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_542_);
return v___x_594_;
}
}
else
{
lean_dec_ref_known(v___x_591_, 3);
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
lean_dec_ref(v_p_564_);
lean_dec(v_k_563_);
lean_dec(v_val_560_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_542_);
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref(v_p_561_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec(v___y_547_);
lean_dec(v___y_542_);
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_560_, v___y_554_, v___y_550_, v___y_538_, v___y_540_, v___y_545_, v___y_544_, v___y_548_, v___y_557_, v___y_551_, v___y_558_);
lean_dec_ref(v___y_551_);
return v___x_619_;
}
}
else
{
lean_object* v_toCold_620_; lean_object* v_options_621_; uint8_t v_hasTrace_622_; 
lean_dec(v___y_559_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec(v___y_547_);
lean_dec(v___y_542_);
v_toCold_620_ = lean_ctor_get(v___y_551_, 0);
v_options_621_ = lean_ctor_get(v_toCold_620_, 2);
v_hasTrace_622_ = lean_ctor_get_uint8(v_options_621_, sizeof(void*)*1);
if (v_hasTrace_622_ == 0)
{
lean_dec_ref(v___y_556_);
v___y_527_ = v___y_541_;
v___y_528_ = v___y_546_;
v___y_529_ = v___y_554_;
v___y_530_ = v___y_548_;
v___y_531_ = v___y_557_;
v___y_532_ = v___y_551_;
v___y_533_ = v___y_558_;
goto v___jp_526_;
}
else
{
lean_object* v_inheritedTraceOptions_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_inheritedTraceOptions_623_ = lean_ctor_get(v_toCold_620_, 11);
v___x_624_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_543_);
lean_inc_ref(v___y_539_);
lean_inc_ref(v___y_549_);
v___x_625_ = l_Lean_Name_mkStr4(v___y_549_, v___y_539_, v___y_543_, v___x_624_);
v___x_626_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_625_);
v___x_627_ = l_Lean_Name_append(v___x_626_, v___x_625_);
v___x_628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_623_, v_options_621_, v___x_627_);
lean_dec(v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v___x_625_);
lean_dec_ref(v___y_556_);
v___y_527_ = v___y_541_;
v___y_528_ = v___y_546_;
v___y_529_ = v___y_554_;
v___y_530_ = v___y_548_;
v___y_531_ = v___y_557_;
v___y_532_ = v___y_551_;
v___y_533_ = v___y_558_;
goto v___jp_526_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_556_, v___y_554_, v___y_551_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_625_, v_a_630_, v___y_548_, v___y_557_, v___y_551_, v___y_558_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref_known(v___x_631_, 1);
v___y_527_ = v___y_541_;
v___y_528_ = v___y_546_;
v___y_529_ = v___y_554_;
v___y_530_ = v___y_548_;
v___y_531_ = v___y_557_;
v___y_532_ = v___y_551_;
v___y_533_ = v___y_558_;
goto v___jp_526_;
}
else
{
lean_dec_ref(v___y_551_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v___y_541_);
return v___x_631_;
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v___x_625_);
lean_dec_ref(v___y_551_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v___y_541_);
v_a_632_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_629_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
}
v___jp_640_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___y_641_);
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_652_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec_ref(v___y_650_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_653_, 0);
lean_dec(v_unused_662_);
v___x_655_ = v___x_653_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_dec(v___x_653_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
return v___x_653_;
}
}
v___jp_673_:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_685_, v___y_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_dvds_697_; lean_object* v_size_698_; uint8_t v___x_699_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v_dvds_697_ = lean_ctor_get(v_a_696_, 5);
lean_inc_ref(v_dvds_697_);
lean_dec(v_a_696_);
v_size_698_ = lean_ctor_get(v_dvds_697_, 2);
v___x_699_ = lean_nat_dec_lt(v___y_680_, v_size_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec_ref(v_dvds_697_);
v___x_700_ = l_outOfBounds___redArg(v___x_672_);
v___y_538_ = v___y_687_;
v___y_539_ = v___y_675_;
v___y_540_ = v___y_688_;
v___y_541_ = v___y_677_;
v___y_542_ = v___y_676_;
v___y_543_ = v___y_678_;
v___y_544_ = v___y_690_;
v___y_545_ = v___y_689_;
v___y_546_ = v___y_684_;
v___y_547_ = v___y_674_;
v___y_548_ = v___y_691_;
v___y_549_ = v___y_679_;
v___y_550_ = v___y_686_;
v___y_551_ = v___y_693_;
v___y_552_ = v___y_680_;
v___y_553_ = v___y_681_;
v___y_554_ = v___y_685_;
v___y_555_ = v___y_683_;
v___y_556_ = v___y_682_;
v___y_557_ = v___y_692_;
v___y_558_ = v___y_694_;
v___y_559_ = v___x_700_;
goto v___jp_537_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_PersistentArray_get_x21___redArg(v___x_672_, v_dvds_697_, v___y_680_);
lean_dec_ref(v_dvds_697_);
v___y_538_ = v___y_687_;
v___y_539_ = v___y_675_;
v___y_540_ = v___y_688_;
v___y_541_ = v___y_677_;
v___y_542_ = v___y_676_;
v___y_543_ = v___y_678_;
v___y_544_ = v___y_690_;
v___y_545_ = v___y_689_;
v___y_546_ = v___y_684_;
v___y_547_ = v___y_674_;
v___y_548_ = v___y_691_;
v___y_549_ = v___y_679_;
v___y_550_ = v___y_686_;
v___y_551_ = v___y_693_;
v___y_552_ = v___y_680_;
v___y_553_ = v___y_681_;
v___y_554_ = v___y_685_;
v___y_555_ = v___y_683_;
v___y_556_ = v___y_682_;
v___y_557_ = v___y_692_;
v___y_558_ = v___y_694_;
v___y_559_ = v___x_701_;
goto v___jp_537_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v___y_693_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v___y_674_);
v_a_702_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_695_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_695_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
v___jp_710_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_511_);
lean_inc_ref(v___y_722_);
v___x_725_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_724_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v_d_728_; lean_object* v_p_729_; uint8_t v___x_730_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_a_726_);
v_d_728_ = lean_ctor_get(v___x_727_, 0);
v_p_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_d_728_);
v___x_730_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_728_, v_p_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v___x_727_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_733_ = lean_int_dec_eq(v_d_728_, v___x_732_);
if (v___x_733_ == 0)
{
if (lean_obj_tag(v_p_729_) == 1)
{
lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v_p_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___x_739_; 
lean_inc_ref(v_p_729_);
lean_inc(v_d_728_);
v_k_734_ = lean_ctor_get(v_p_729_, 0);
lean_inc(v_k_734_);
v_v_735_ = lean_ctor_get(v_p_729_, 1);
lean_inc_n(v_v_735_, 3);
v_p_736_ = lean_ctor_get(v_p_729_, 2);
lean_inc_ref(v_p_736_);
lean_inc_ref_n(v___x_727_, 2);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_737_, 0, v___x_727_);
lean_closure_set(v___f_737_, 1, v_v_735_);
v___f_738_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_738_, 0, v_v_735_);
v___x_739_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v___x_727_, v___y_714_, v___y_722_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; uint8_t v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = 0;
v___x_742_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
v___x_743_ = l_Lean_instBEqLBool_beq(v___x_742_, v___x_741_);
if (v___x_743_ == 0)
{
v___y_674_ = v_d_728_;
v___y_675_ = v___y_711_;
v___y_676_ = v_k_734_;
v___y_677_ = v_p_729_;
v___y_678_ = v___y_712_;
v___y_679_ = v___y_713_;
v___y_680_ = v_v_735_;
v___y_681_ = v___f_738_;
v___y_682_ = v___x_727_;
v___y_683_ = v_p_736_;
v___y_684_ = v___f_737_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_717_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_719_;
v___y_691_ = v___y_720_;
v___y_692_ = v___y_721_;
v___y_693_ = v___y_722_;
v___y_694_ = v___y_723_;
goto v___jp_673_;
}
else
{
lean_object* v___x_744_; 
lean_inc(v_v_735_);
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_735_, v___y_714_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
v___y_674_ = v_d_728_;
v___y_675_ = v___y_711_;
v___y_676_ = v_k_734_;
v___y_677_ = v_p_729_;
v___y_678_ = v___y_712_;
v___y_679_ = v___y_713_;
v___y_680_ = v_v_735_;
v___y_681_ = v___f_738_;
v___y_682_ = v___x_727_;
v___y_683_ = v_p_736_;
v___y_684_ = v___f_737_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_717_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_719_;
v___y_691_ = v___y_720_;
v___y_692_ = v___y_721_;
v___y_693_ = v___y_722_;
v___y_694_ = v___y_723_;
goto v___jp_673_;
}
else
{
lean_dec_ref(v___f_738_);
lean_dec_ref(v___f_737_);
lean_dec_ref(v_p_736_);
lean_dec(v_v_735_);
lean_dec_ref_known(v_p_729_, 3);
lean_dec(v_k_734_);
lean_dec(v_d_728_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
return v___x_744_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___f_738_);
lean_dec_ref(v___f_737_);
lean_dec_ref(v_p_736_);
lean_dec(v_v_735_);
lean_dec_ref_known(v_p_729_, 3);
lean_dec(v_k_734_);
lean_dec(v_d_728_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
v_a_745_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_739_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_739_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v___x_727_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec_ref(v___y_722_);
return v___x_753_;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc_ref(v_p_729_);
v___x_754_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_727_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_p_729_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_inc(v___y_723_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc(v___y_714_);
v___x_756_ = lean_grind_cutsat_assert_eq(v___x_755_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_756_, 0);
lean_dec(v_unused_765_);
v___x_758_ = v___x_756_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_dec(v___x_756_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_box(0);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
return v___x_756_;
}
}
}
else
{
lean_object* v_toCold_766_; lean_object* v_options_767_; uint8_t v_hasTrace_768_; 
v_toCold_766_ = lean_ctor_get(v___y_722_, 0);
v_options_767_ = lean_ctor_get(v_toCold_766_, 2);
v_hasTrace_768_ = lean_ctor_get_uint8(v_options_767_, sizeof(void*)*1);
if (v_hasTrace_768_ == 0)
{
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
goto v___jp_523_;
}
else
{
lean_object* v_inheritedTraceOptions_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_inheritedTraceOptions_769_ = lean_ctor_get(v_toCold_766_, 11);
v___x_770_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc_ref(v___y_713_);
v___x_771_ = l_Lean_Name_mkStr4(v___y_713_, v___y_711_, v___y_712_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_771_);
v___x_773_ = l_Lean_Name_append(v___x_772_, v___x_771_);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_769_, v_options_767_, v___x_773_);
lean_dec(v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v___x_771_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
goto v___jp_523_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_727_, v___y_714_, v___y_722_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_771_, v_a_776_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec_ref(v___y_722_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref_known(v___x_777_, 1);
goto v___jp_523_;
}
else
{
return v___x_777_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___x_771_);
lean_dec_ref(v___y_722_);
v_a_778_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_775_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_786_; lean_object* v_options_787_; uint8_t v_hasTrace_788_; 
v_toCold_786_ = lean_ctor_get(v___y_722_, 0);
v_options_787_ = lean_ctor_get(v_toCold_786_, 2);
v_hasTrace_788_ = lean_ctor_get_uint8(v_options_787_, sizeof(void*)*1);
if (v_hasTrace_788_ == 0)
{
v___y_641_ = v___x_727_;
v___y_642_ = v___y_714_;
v___y_643_ = v___y_715_;
v___y_644_ = v___y_716_;
v___y_645_ = v___y_717_;
v___y_646_ = v___y_718_;
v___y_647_ = v___y_719_;
v___y_648_ = v___y_720_;
v___y_649_ = v___y_721_;
v___y_650_ = v___y_722_;
v___y_651_ = v___y_723_;
goto v___jp_640_;
}
else
{
lean_object* v_inheritedTraceOptions_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_inheritedTraceOptions_789_ = lean_ctor_get(v_toCold_786_, 11);
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc_ref(v___y_713_);
v___x_791_ = l_Lean_Name_mkStr4(v___y_713_, v___y_711_, v___y_712_, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_791_);
v___x_793_ = l_Lean_Name_append(v___x_792_, v___x_791_);
v___x_794_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_789_, v_options_787_, v___x_793_);
lean_dec(v___x_793_);
if (v___x_794_ == 0)
{
lean_dec(v___x_791_);
v___y_641_ = v___x_727_;
v___y_642_ = v___y_714_;
v___y_643_ = v___y_715_;
v___y_644_ = v___y_716_;
v___y_645_ = v___y_717_;
v___y_646_ = v___y_718_;
v___y_647_ = v___y_719_;
v___y_648_ = v___y_720_;
v___y_649_ = v___y_721_;
v___y_650_ = v___y_722_;
v___y_651_ = v___y_723_;
goto v___jp_640_;
}
else
{
lean_object* v___x_795_; 
lean_inc_ref(v___x_727_);
v___x_795_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_727_, v___y_714_, v___y_722_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___x_797_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_791_, v_a_796_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_dec_ref_known(v___x_797_, 1);
v___y_641_ = v___x_727_;
v___y_642_ = v___y_714_;
v___y_643_ = v___y_715_;
v___y_644_ = v___y_716_;
v___y_645_ = v___y_717_;
v___y_646_ = v___y_718_;
v___y_647_ = v___y_719_;
v___y_648_ = v___y_720_;
v___y_649_ = v___y_721_;
v___y_650_ = v___y_722_;
v___y_651_ = v___y_723_;
goto v___jp_640_;
}
else
{
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
return v___x_797_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___x_791_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v___y_722_);
v_a_798_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_795_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v___y_722_);
v_a_806_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_725_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_725_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_currRecDepth_664_, v___x_815_);
lean_dec(v_currRecDepth_664_);
v___x_817_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_817_, 0, v_toCold_663_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
lean_ctor_set(v___x_817_, 2, v_ref_665_);
lean_ctor_set_uint16(v___x_817_, sizeof(void*)*3, v_optionFlags_666_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*3 + 2, v_suppressElabErrors_667_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*3 + 3, v_isRecordingDeps_668_);
v___x_818_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_512_, v___x_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_846_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_846_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_846_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_846_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_823_ == 0)
{
uint8_t v_hasTrace_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_821_);
v_hasTrace_824_ = lean_ctor_get_uint8(v_options_669_, sizeof(void*)*1);
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_827_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_824_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_671_);
lean_dec_ref(v_options_669_);
v___y_711_ = v___x_826_;
v___y_712_ = v___x_827_;
v___y_713_ = v___x_825_;
v___y_714_ = v_a_512_;
v___y_715_ = v_a_513_;
v___y_716_ = v_a_514_;
v___y_717_ = v_a_515_;
v___y_718_ = v_a_516_;
v___y_719_ = v_a_517_;
v___y_720_ = v_a_518_;
v___y_721_ = v_a_519_;
v___y_722_ = v___x_817_;
v___y_723_ = v_a_521_;
goto v___jp_710_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_829_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_671_, v_options_669_, v___x_829_);
lean_dec_ref(v_options_669_);
lean_dec_ref(v_inheritedTraceOptions_671_);
if (v___x_830_ == 0)
{
v___y_711_ = v___x_826_;
v___y_712_ = v___x_827_;
v___y_713_ = v___x_825_;
v___y_714_ = v_a_512_;
v___y_715_ = v_a_513_;
v___y_716_ = v_a_514_;
v___y_717_ = v_a_515_;
v___y_718_ = v_a_516_;
v___y_719_ = v_a_517_;
v___y_720_ = v_a_518_;
v___y_721_ = v_a_519_;
v___y_722_ = v___x_817_;
v___y_723_ = v_a_521_;
goto v___jp_710_;
}
else
{
lean_object* v___x_831_; 
lean_inc_ref(v_c_511_);
v___x_831_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_511_, v_a_512_, v___x_817_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_828_, v_a_832_, v_a_518_, v_a_519_, v___x_817_, v_a_521_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec_ref_known(v___x_833_, 1);
v___y_711_ = v___x_826_;
v___y_712_ = v___x_827_;
v___y_713_ = v___x_825_;
v___y_714_ = v_a_512_;
v___y_715_ = v_a_513_;
v___y_716_ = v_a_514_;
v___y_717_ = v_a_515_;
v___y_718_ = v_a_516_;
v___y_719_ = v_a_517_;
v___y_720_ = v_a_518_;
v___y_721_ = v_a_519_;
v___y_722_ = v___x_817_;
v___y_723_ = v_a_521_;
goto v___jp_710_;
}
else
{
lean_dec_ref_known(v___x_817_, 3);
lean_dec_ref(v_c_511_);
return v___x_833_;
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref_known(v___x_817_, 3);
lean_dec_ref(v_c_511_);
v_a_834_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_831_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec_ref_known(v___x_817_, 3);
lean_dec_ref(v_inheritedTraceOptions_671_);
lean_dec_ref(v_options_669_);
lean_dec_ref(v_c_511_);
v___x_842_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_842_);
v___x_844_ = v___x_821_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref_known(v___x_817_, 3);
lean_dec_ref(v_inheritedTraceOptions_671_);
lean_dec_ref(v_options_669_);
lean_dec_ref(v_c_511_);
v_a_847_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_818_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_818_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec(v_a_860_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_d_884_; lean_object* v_p_885_; lean_object* v___x_886_; 
v_d_884_ = lean_ctor_get(v_c_872_, 0);
v_p_885_ = lean_ctor_get(v_c_872_, 1);
lean_inc_ref(v_p_885_);
v___x_886_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_885_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
if (lean_obj_tag(v_a_887_) == 1)
{
lean_object* v_val_888_; lean_object* v_snd_889_; lean_object* v_fst_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_d_884_);
v_val_888_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v_a_887_, 1);
v_snd_889_ = lean_ctor_get(v_val_888_, 1);
lean_inc(v_snd_889_);
v_fst_890_ = lean_ctor_get(v_val_888_, 0);
lean_inc(v_fst_890_);
lean_dec(v_val_888_);
v_fst_891_ = lean_ctor_get(v_snd_889_, 0);
lean_inc(v_fst_891_);
v_snd_892_ = lean_ctor_get(v_snd_889_, 1);
lean_inc(v_snd_892_);
lean_dec(v_snd_889_);
v___x_893_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_893_, 0, v_c_872_);
lean_ctor_set(v___x_893_, 1, v_fst_890_);
lean_ctor_set(v___x_893_, 2, v_fst_891_);
v___x_894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_894_, 0, v_d_884_);
lean_ctor_set(v___x_894_, 1, v_snd_892_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
lean_inc_ref(v_a_881_);
v___x_895_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_894_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
lean_dec(v_a_887_);
lean_inc_ref(v_a_881_);
v___x_896_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_896_;
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_c_872_);
v_a_897_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_886_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_886_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
return v_res_917_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_box(0);
v___x_933_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_934_ = l_Lean_mkConst(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_956_; 
lean_inc_ref(v_e_938_);
v___x_956_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_938_, v_a_946_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_a_957_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v___x_958_);
lean_dec_ref(v_e_938_);
goto v___jp_950_;
}
else
{
lean_object* v_arg_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_arg_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc_ref(v_arg_960_);
v___x_961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_962_ = l_Lean_Expr_isApp(v___x_961_);
if (v___x_962_ == 0)
{
lean_dec_ref(v___x_961_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
goto v___jp_950_;
}
else
{
lean_object* v_arg_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_arg_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc_ref(v_arg_963_);
v___x_964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_961_);
v___x_965_ = l_Lean_Expr_isApp(v___x_964_);
if (v___x_965_ == 0)
{
lean_dec_ref(v___x_964_);
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
goto v___jp_950_;
}
else
{
lean_object* v_arg_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_arg_966_ = lean_ctor_get(v___x_964_, 1);
lean_inc_ref(v_arg_966_);
v___x_967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_964_);
v___x_968_ = l_Lean_Expr_isApp(v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v___x_967_);
lean_dec_ref(v_arg_966_);
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
goto v___jp_950_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_967_);
v___x_970_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_971_ = l_Lean_Expr_isConstOf(v___x_969_, v___x_970_);
lean_dec_ref(v___x_969_);
if (v___x_971_ == 0)
{
lean_dec_ref(v_arg_966_);
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
goto v___jp_950_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_966_, v_a_946_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1073_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1073_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1073_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
uint8_t v___x_977_; 
v___x_977_ = lean_unbox(v_a_973_);
lean_dec(v_a_973_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v___x_978_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v___x_982_; 
lean_del_object(v___x_975_);
lean_inc_ref(v_arg_963_);
v___x_982_ = l_Lean_Meta_getIntValue_x3f(v_arg_963_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
if (lean_obj_tag(v_a_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1049_; 
v_val_984_ = lean_ctor_get(v_a_983_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_986_ = v_a_983_;
v_isShared_987_ = v_isSharedCheck_1049_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v_a_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1049_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; 
lean_inc_ref(v_e_938_);
v___x_988_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_938_, v_a_939_, v_a_943_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; uint8_t v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = lean_unbox(v_a_989_);
lean_dec(v_a_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_del_object(v___x_986_);
lean_dec(v_val_984_);
lean_inc_ref(v_e_938_);
v___x_991_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_938_, v_a_939_, v_a_943_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1017_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1017_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1017_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___x_996_; 
v___x_996_ = lean_unbox(v_a_992_);
lean_dec(v_a_992_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v___x_997_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v___x_1001_; 
lean_del_object(v___x_994_);
lean_inc_ref(v_e_938_);
v___x_1001_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_1004_ = l_Lean_eagerReflBoolTrue;
v___x_1005_ = l_Lean_Meta_mkOfEqFalseCore(v_e_938_, v_a_1002_);
v___x_1006_ = l_Lean_mkApp4(v___x_1003_, v_arg_963_, v_arg_960_, v___x_1004_, v___x_1005_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = l_Lean_Meta_Grind_pushNewFact(v___x_1006_, v___x_1007_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v_a_1009_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1001_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1001_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v_a_1018_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_991_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_991_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v_arg_963_);
v___x_1026_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_960_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 0, v_e_938_);
v___x_1029_ = v___x_986_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_e_938_);
v___x_1029_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1030_, 0, v_val_984_);
lean_ctor_set(v___x_1030_, 1, v_a_1027_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
v___x_1031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1030_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_1031_;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_del_object(v___x_986_);
lean_dec(v_val_984_);
lean_dec_ref(v_e_938_);
v_a_1033_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1026_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1026_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_del_object(v___x_986_);
lean_dec(v_val_984_);
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v_a_1041_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_988_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_988_);
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
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_a_983_);
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
v___x_1050_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1051_ = l_Lean_indentExpr(v_e_938_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_943_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; uint8_t v_verbose_1055_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v_verbose_1055_ = lean_ctor_get_uint8(v_a_1054_, 0);
lean_dec(v_a_1054_);
if (v_verbose_1055_ == 0)
{
lean_dec_ref_known(v___x_1052_, 2);
goto v___jp_953_;
}
else
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_Sym_reportIssue(v___x_1052_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_dec_ref_known(v___x_1056_, 1);
goto v___jp_953_;
}
else
{
return v___x_1056_;
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref_known(v___x_1052_, 2);
v_a_1057_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1053_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1053_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v_a_1065_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_982_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_982_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_arg_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_e_938_);
v_a_1074_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_972_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_972_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
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
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_e_938_);
v_a_1082_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_956_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_956_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec(v_a_1091_);
return v_res_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1110_ = l_Lean_mkConst(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1119_ = l_Lean_mkConst(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
lean_inc_ref(v_e_1120_);
v___x_1138_ = l_Lean_Expr_cleanupAnnotations(v_e_1120_);
v___x_1139_ = l_Lean_Expr_isApp(v___x_1138_);
if (v___x_1139_ == 0)
{
lean_dec_ref(v___x_1138_);
lean_dec_ref(v_e_1120_);
goto v___jp_1132_;
}
else
{
lean_object* v_arg_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_arg_1140_ = lean_ctor_get(v___x_1138_, 1);
lean_inc_ref(v_arg_1140_);
v___x_1141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1138_);
v___x_1142_ = l_Lean_Expr_isApp(v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
goto v___jp_1132_;
}
else
{
lean_object* v_arg_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_arg_1143_ = lean_ctor_get(v___x_1141_, 1);
lean_inc_ref(v_arg_1143_);
v___x_1144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1141_);
v___x_1145_ = l_Lean_Expr_isApp(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
goto v___jp_1132_;
}
else
{
lean_object* v_arg_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_arg_1146_ = lean_ctor_get(v___x_1144_, 1);
lean_inc_ref(v_arg_1146_);
v___x_1147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1144_);
v___x_1148_ = l_Lean_Expr_isApp(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec_ref(v___x_1147_);
lean_dec_ref(v_arg_1146_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
goto v___jp_1132_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1149_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1147_);
v___x_1150_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1151_ = l_Lean_Expr_isConstOf(v___x_1149_, v___x_1150_);
lean_dec_ref(v___x_1149_);
if (v___x_1151_ == 0)
{
lean_dec_ref(v_arg_1146_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
goto v___jp_1132_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1146_, v_a_1128_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1284_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1284_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1284_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_unbox(v_a_1153_);
lean_dec(v_a_1153_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v___x_1158_ = lean_box(0);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; 
lean_del_object(v___x_1155_);
v___x_1162_ = l_Lean_Meta_getNatValue_x3f(v_arg_1143_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
if (lean_obj_tag(v_a_1163_) == 1)
{
lean_object* v_val_1164_; lean_object* v___x_1165_; 
v_val_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v_a_1163_, 1);
lean_inc_ref(v_e_1120_);
v___x_1165_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1120_, v_a_1121_, v_a_1125_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; uint8_t v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec(v_val_1164_);
lean_inc_ref(v_e_1120_);
v___x_1168_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1120_, v_a_1121_, v_a_1125_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1193_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1193_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1193_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v___x_1174_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1178_; 
lean_del_object(v___x_1171_);
lean_inc_ref(v_e_1120_);
v___x_1178_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1181_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1120_, v_a_1179_);
v___x_1182_ = l_Lean_mkApp3(v___x_1180_, v_arg_1143_, v_arg_1140_, v___x_1181_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_Meta_Grind_pushNewFact(v___x_1182_, v___x_1183_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1184_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1185_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1178_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1178_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1194_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1168_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1168_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_inc_ref(v_arg_1143_);
v___x_1202_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1143_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_fst_1204_; lean_object* v_snd_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_fst_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_fst_1204_);
v_snd_1205_ = lean_ctor_get(v_a_1203_, 1);
lean_inc(v_snd_1205_);
lean_dec(v_a_1203_);
lean_inc_ref(v_arg_1140_);
v___x_1206_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1140_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v_fst_1208_; lean_object* v_snd_1209_; lean_object* v___x_1210_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v_fst_1208_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_fst_1208_);
v_snd_1209_ = lean_ctor_get(v_a_1207_, 1);
lean_inc(v_snd_1209_);
lean_dec(v_a_1207_);
v___x_1210_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
lean_inc(v_fst_1208_);
v___x_1212_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1208_, v_a_1211_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Int_Internal_Linear_Expr_norm(v_a_1213_);
v___x_1215_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1216_ = l_Lean_mkApp6(v___x_1215_, v_arg_1143_, v_arg_1140_, v_fst_1204_, v_fst_1208_, v_snd_1205_, v_snd_1209_);
lean_inc(v_val_1164_);
v___x_1217_ = lean_nat_to_int(v_val_1164_);
v___x_1218_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1218_, 0, v_e_1120_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
lean_ctor_set(v___x_1218_, 2, v_val_1164_);
lean_ctor_set(v___x_1218_, 3, v_a_1213_);
v___x_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1214_);
lean_ctor_set(v___x_1219_, 2, v___x_1218_);
v___x_1220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1219_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1220_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_snd_1209_);
lean_dec(v_fst_1208_);
lean_dec(v_snd_1205_);
lean_dec(v_fst_1204_);
lean_dec(v_val_1164_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1221_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1212_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1212_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_snd_1209_);
lean_dec(v_fst_1208_);
lean_dec(v_snd_1205_);
lean_dec(v_fst_1204_);
lean_dec(v_val_1164_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1229_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1210_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1210_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_snd_1205_);
lean_dec(v_fst_1204_);
lean_dec(v_val_1164_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1237_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1206_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1206_);
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
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_val_1164_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1245_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1202_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1202_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_val_1164_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1253_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1165_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1165_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_a_1163_);
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
v___x_1261_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1262_ = l_Lean_indentExpr(v_e_1120_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1125_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; uint8_t v_verbose_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v_verbose_1266_ = lean_ctor_get_uint8(v_a_1265_, 0);
lean_dec(v_a_1265_);
if (v_verbose_1266_ == 0)
{
lean_dec_ref_known(v___x_1263_, 2);
goto v___jp_1135_;
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Meta_Sym_reportIssue(v___x_1263_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_dec_ref_known(v___x_1267_, 1);
goto v___jp_1135_;
}
else
{
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref_known(v___x_1263_, 2);
v_a_1268_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1264_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1264_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1276_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1162_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1162_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_arg_1143_);
lean_dec_ref(v_arg_1140_);
lean_dec_ref(v_e_1120_);
v_a_1285_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1152_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1152_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
}
v___jp_1132_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
v___jp_1135_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec(v_a_1294_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1311_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1359_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1359_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1359_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
uint8_t v_lia_1328_; 
v_lia_1328_ = lean_ctor_get_uint8(v_a_1324_, sizeof(void*)*17 + 24);
lean_dec(v_a_1324_);
if (v_lia_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
lean_dec_ref(v_e_1308_);
v___x_1329_ = lean_box(0);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
else
{
lean_object* v___x_1333_; 
lean_del_object(v___x_1326_);
lean_inc_ref(v_e_1308_);
v___x_1333_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1308_, v_a_1316_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = l_Lean_Expr_cleanupAnnotations(v_a_1334_);
v___x_1336_ = l_Lean_Expr_isApp(v___x_1335_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_e_1308_);
goto v___jp_1320_;
}
else
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1335_);
v___x_1338_ = l_Lean_Expr_isApp(v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_e_1308_);
goto v___jp_1320_;
}
else
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1337_);
v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_e_1308_);
goto v___jp_1320_;
}
else
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
v___x_1342_ = l_Lean_Expr_isApp(v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_e_1308_);
goto v___jp_1320_;
}
else
{
lean_object* v_arg_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_arg_1343_ = lean_ctor_get(v___x_1341_, 1);
lean_inc_ref(v_arg_1343_);
v___x_1344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1341_);
v___x_1345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1346_ = l_Lean_Expr_isConstOf(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1344_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v_arg_1343_);
lean_dec_ref(v_e_1308_);
goto v___jp_1320_;
}
else
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1348_ = l_Lean_Expr_isConstOf(v_arg_1343_, v___x_1347_);
lean_dec_ref(v_arg_1343_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1350_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_e_1308_);
v_a_1351_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1333_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1333_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_e_1308_);
v_a_1360_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1323_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1323_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
v___jp_1320_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec(v_a_1369_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1384_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1382_, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1386_;
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
