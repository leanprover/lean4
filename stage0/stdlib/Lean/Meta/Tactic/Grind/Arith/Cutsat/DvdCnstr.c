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
lean_object* v_p_368_; lean_object* v_toCold_369_; lean_object* v_currRecDepth_370_; lean_object* v_ref_371_; uint16_t v_optionFlags_372_; uint8_t v_suppressElabErrors_373_; uint8_t v_checkDeprecated_374_; uint8_t v_isRecordingDeps_375_; lean_object* v_maxRecDepth_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_p_368_ = lean_ctor_get(v_c_356_, 1);
v_toCold_369_ = lean_ctor_get(v_a_365_, 0);
lean_inc_ref(v_toCold_369_);
v_currRecDepth_370_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_currRecDepth_370_);
v_ref_371_ = lean_ctor_get(v_a_365_, 2);
lean_inc(v_ref_371_);
v_optionFlags_372_ = lean_ctor_get_uint16(v_a_365_, sizeof(void*)*3);
v_suppressElabErrors_373_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*3 + 2);
v_checkDeprecated_374_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*3 + 3);
v_isRecordingDeps_375_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_365_);
v_maxRecDepth_407_ = lean_ctor_get(v_toCold_369_, 3);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_nat_dec_eq(v_maxRecDepth_407_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_eq(v_currRecDepth_370_, v_maxRecDepth_407_);
if (v___x_410_ == 0)
{
goto v___jp_376_;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_currRecDepth_370_);
lean_dec_ref(v_toCold_369_);
lean_dec_ref(v_c_356_);
v___x_411_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_371_);
return v___x_411_;
}
}
else
{
goto v___jp_376_;
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_currRecDepth_370_, v___x_377_);
lean_dec(v_currRecDepth_370_);
v___x_379_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_379_, 0, v_toCold_369_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_ctor_set(v___x_379_, 2, v_ref_371_);
lean_ctor_set_uint16(v___x_379_, sizeof(void*)*3, v_optionFlags_372_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 2, v_suppressElabErrors_373_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 3, v_checkDeprecated_374_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 4, v_isRecordingDeps_375_);
lean_inc_ref(v_p_368_);
v___x_380_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_368_, v_a_357_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_398_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_a_381_) == 1)
{
lean_object* v_val_385_; lean_object* v_snd_386_; lean_object* v_snd_387_; lean_object* v_fst_388_; lean_object* v_fst_389_; lean_object* v_p_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_del_object(v___x_383_);
v_val_385_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v_a_381_, 1);
v_snd_386_ = lean_ctor_get(v_val_385_, 1);
lean_inc(v_snd_386_);
v_snd_387_ = lean_ctor_get(v_snd_386_, 1);
lean_inc(v_snd_387_);
v_fst_388_ = lean_ctor_get(v_val_385_, 0);
lean_inc(v_fst_388_);
lean_dec(v_val_385_);
v_fst_389_ = lean_ctor_get(v_snd_386_, 0);
lean_inc(v_fst_389_);
lean_dec(v_snd_386_);
v_p_390_ = lean_ctor_get(v_snd_387_, 0);
v___x_391_ = l_Int_Internal_Linear_Poly_coeff(v_p_390_, v_fst_389_);
v___x_392_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_391_, v_fst_389_, v_snd_387_, v_fst_388_, v_c_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v___x_379_, v_a_366_);
lean_dec(v_fst_388_);
lean_dec(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v_c_356_ = v_a_393_;
v_a_365_ = v___x_379_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_379_, 3);
return v___x_392_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v_a_381_);
lean_dec_ref_known(v___x_379_, 3);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_c_356_);
v___x_396_ = v___x_383_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_c_356_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref_known(v___x_379_, 3);
lean_dec_ref(v_c_356_);
v_a_399_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_380_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_380_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec(v_a_413_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v___x_425_, lean_object* v_v_426_, lean_object* v_s_427_){
_start:
{
lean_object* v_vars_428_; lean_object* v_varMap_429_; lean_object* v_varsHistory_430_; lean_object* v_natToIntMap_431_; lean_object* v_natDef_432_; lean_object* v_dvds_433_; lean_object* v_lowers_434_; lean_object* v_uppers_435_; lean_object* v_diseqs_436_; lean_object* v_elimEqs_437_; lean_object* v_elimStack_438_; lean_object* v_occurs_439_; lean_object* v_assignment_440_; lean_object* v_nextCnstrId_441_; uint8_t v_caseSplits_442_; lean_object* v_steps_443_; lean_object* v_penalties_444_; lean_object* v_numReorderRequests_445_; lean_object* v_conflict_x3f_446_; lean_object* v_diseqSplits_447_; lean_object* v_divMod_448_; uint8_t v_usedCommRing_449_; lean_object* v_nonlinearOccs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_459_; 
v_vars_428_ = lean_ctor_get(v_s_427_, 0);
v_varMap_429_ = lean_ctor_get(v_s_427_, 1);
v_varsHistory_430_ = lean_ctor_get(v_s_427_, 2);
v_natToIntMap_431_ = lean_ctor_get(v_s_427_, 3);
v_natDef_432_ = lean_ctor_get(v_s_427_, 4);
v_dvds_433_ = lean_ctor_get(v_s_427_, 5);
v_lowers_434_ = lean_ctor_get(v_s_427_, 6);
v_uppers_435_ = lean_ctor_get(v_s_427_, 7);
v_diseqs_436_ = lean_ctor_get(v_s_427_, 8);
v_elimEqs_437_ = lean_ctor_get(v_s_427_, 9);
v_elimStack_438_ = lean_ctor_get(v_s_427_, 10);
v_occurs_439_ = lean_ctor_get(v_s_427_, 11);
v_assignment_440_ = lean_ctor_get(v_s_427_, 12);
v_nextCnstrId_441_ = lean_ctor_get(v_s_427_, 13);
v_caseSplits_442_ = lean_ctor_get_uint8(v_s_427_, sizeof(void*)*21);
v_steps_443_ = lean_ctor_get(v_s_427_, 14);
v_penalties_444_ = lean_ctor_get(v_s_427_, 15);
v_numReorderRequests_445_ = lean_ctor_get(v_s_427_, 16);
v_conflict_x3f_446_ = lean_ctor_get(v_s_427_, 17);
v_diseqSplits_447_ = lean_ctor_get(v_s_427_, 18);
v_divMod_448_ = lean_ctor_get(v_s_427_, 19);
v_usedCommRing_449_ = lean_ctor_get_uint8(v_s_427_, sizeof(void*)*21 + 1);
v_nonlinearOccs_450_ = lean_ctor_get(v_s_427_, 20);
v_isSharedCheck_459_ = !lean_is_exclusive(v_s_427_);
if (v_isSharedCheck_459_ == 0)
{
v___x_452_ = v_s_427_;
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_nonlinearOccs_450_);
lean_inc(v_divMod_448_);
lean_inc(v_diseqSplits_447_);
lean_inc(v_conflict_x3f_446_);
lean_inc(v_numReorderRequests_445_);
lean_inc(v_penalties_444_);
lean_inc(v_steps_443_);
lean_inc(v_nextCnstrId_441_);
lean_inc(v_assignment_440_);
lean_inc(v_occurs_439_);
lean_inc(v_elimStack_438_);
lean_inc(v_elimEqs_437_);
lean_inc(v_diseqs_436_);
lean_inc(v_uppers_435_);
lean_inc(v_lowers_434_);
lean_inc(v_dvds_433_);
lean_inc(v_natDef_432_);
lean_inc(v_natToIntMap_431_);
lean_inc(v_varsHistory_430_);
lean_inc(v_varMap_429_);
lean_inc(v_vars_428_);
lean_dec(v_s_427_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_425_);
v___x_455_ = l_Lean_PersistentArray_set___redArg(v_dvds_433_, v_v_426_, v___x_454_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 5, v___x_455_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_vars_428_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_varMap_429_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_varsHistory_430_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_natToIntMap_431_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_natDef_432_);
lean_ctor_set(v_reuseFailAlloc_458_, 5, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_458_, 6, v_lowers_434_);
lean_ctor_set(v_reuseFailAlloc_458_, 7, v_uppers_435_);
lean_ctor_set(v_reuseFailAlloc_458_, 8, v_diseqs_436_);
lean_ctor_set(v_reuseFailAlloc_458_, 9, v_elimEqs_437_);
lean_ctor_set(v_reuseFailAlloc_458_, 10, v_elimStack_438_);
lean_ctor_set(v_reuseFailAlloc_458_, 11, v_occurs_439_);
lean_ctor_set(v_reuseFailAlloc_458_, 12, v_assignment_440_);
lean_ctor_set(v_reuseFailAlloc_458_, 13, v_nextCnstrId_441_);
lean_ctor_set(v_reuseFailAlloc_458_, 14, v_steps_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 15, v_penalties_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 16, v_numReorderRequests_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 17, v_conflict_x3f_446_);
lean_ctor_set(v_reuseFailAlloc_458_, 18, v_diseqSplits_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 19, v_divMod_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 20, v_nonlinearOccs_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*21, v_caseSplits_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*21 + 1, v_usedCommRing_449_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v___x_460_, lean_object* v_v_461_, lean_object* v_s_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v___x_460_, v_v_461_, v_s_462_);
lean_dec(v_v_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_464_, lean_object* v_s_465_){
_start:
{
lean_object* v_vars_466_; lean_object* v_varMap_467_; lean_object* v_varsHistory_468_; lean_object* v_natToIntMap_469_; lean_object* v_natDef_470_; lean_object* v_dvds_471_; lean_object* v_lowers_472_; lean_object* v_uppers_473_; lean_object* v_diseqs_474_; lean_object* v_elimEqs_475_; lean_object* v_elimStack_476_; lean_object* v_occurs_477_; lean_object* v_assignment_478_; lean_object* v_nextCnstrId_479_; uint8_t v_caseSplits_480_; lean_object* v_steps_481_; lean_object* v_penalties_482_; lean_object* v_numReorderRequests_483_; lean_object* v_conflict_x3f_484_; lean_object* v_diseqSplits_485_; lean_object* v_divMod_486_; uint8_t v_usedCommRing_487_; lean_object* v_nonlinearOccs_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v_vars_466_ = lean_ctor_get(v_s_465_, 0);
v_varMap_467_ = lean_ctor_get(v_s_465_, 1);
v_varsHistory_468_ = lean_ctor_get(v_s_465_, 2);
v_natToIntMap_469_ = lean_ctor_get(v_s_465_, 3);
v_natDef_470_ = lean_ctor_get(v_s_465_, 4);
v_dvds_471_ = lean_ctor_get(v_s_465_, 5);
v_lowers_472_ = lean_ctor_get(v_s_465_, 6);
v_uppers_473_ = lean_ctor_get(v_s_465_, 7);
v_diseqs_474_ = lean_ctor_get(v_s_465_, 8);
v_elimEqs_475_ = lean_ctor_get(v_s_465_, 9);
v_elimStack_476_ = lean_ctor_get(v_s_465_, 10);
v_occurs_477_ = lean_ctor_get(v_s_465_, 11);
v_assignment_478_ = lean_ctor_get(v_s_465_, 12);
v_nextCnstrId_479_ = lean_ctor_get(v_s_465_, 13);
v_caseSplits_480_ = lean_ctor_get_uint8(v_s_465_, sizeof(void*)*21);
v_steps_481_ = lean_ctor_get(v_s_465_, 14);
v_penalties_482_ = lean_ctor_get(v_s_465_, 15);
v_numReorderRequests_483_ = lean_ctor_get(v_s_465_, 16);
v_conflict_x3f_484_ = lean_ctor_get(v_s_465_, 17);
v_diseqSplits_485_ = lean_ctor_get(v_s_465_, 18);
v_divMod_486_ = lean_ctor_get(v_s_465_, 19);
v_usedCommRing_487_ = lean_ctor_get_uint8(v_s_465_, sizeof(void*)*21 + 1);
v_nonlinearOccs_488_ = lean_ctor_get(v_s_465_, 20);
v_isSharedCheck_497_ = !lean_is_exclusive(v_s_465_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v_s_465_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_nonlinearOccs_488_);
lean_inc(v_divMod_486_);
lean_inc(v_diseqSplits_485_);
lean_inc(v_conflict_x3f_484_);
lean_inc(v_numReorderRequests_483_);
lean_inc(v_penalties_482_);
lean_inc(v_steps_481_);
lean_inc(v_nextCnstrId_479_);
lean_inc(v_assignment_478_);
lean_inc(v_occurs_477_);
lean_inc(v_elimStack_476_);
lean_inc(v_elimEqs_475_);
lean_inc(v_diseqs_474_);
lean_inc(v_uppers_473_);
lean_inc(v_lowers_472_);
lean_inc(v_dvds_471_);
lean_inc(v_natDef_470_);
lean_inc(v_natToIntMap_469_);
lean_inc(v_varsHistory_468_);
lean_inc(v_varMap_467_);
lean_inc(v_vars_466_);
lean_dec(v_s_465_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_box(0);
v___x_493_ = l_Lean_PersistentArray_set___redArg(v_dvds_471_, v_v_464_, v___x_492_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 5, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_vars_466_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_varMap_467_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_varsHistory_468_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_natToIntMap_469_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_natDef_470_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_lowers_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_uppers_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_diseqs_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_elimEqs_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 10, v_elimStack_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 11, v_occurs_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 12, v_assignment_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 13, v_nextCnstrId_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 14, v_steps_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 15, v_penalties_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 16, v_numReorderRequests_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 17, v_conflict_x3f_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 18, v_diseqSplits_485_);
lean_ctor_set(v_reuseFailAlloc_496_, 19, v_divMod_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 20, v_nonlinearOccs_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*21, v_caseSplits_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*21 + 1, v_usedCommRing_487_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_498_, lean_object* v_s_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_498_, v_s_499_);
lean_dec(v_v_498_);
return v_res_500_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_510_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_511_ = l_Lean_Name_append(v___x_510_, v___x_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v_toCold_664_; lean_object* v_currRecDepth_665_; lean_object* v_ref_666_; uint16_t v_optionFlags_667_; uint8_t v_suppressElabErrors_668_; uint8_t v_checkDeprecated_669_; uint8_t v_isRecordingDeps_670_; lean_object* v_options_671_; lean_object* v_maxRecDepth_672_; lean_object* v_inheritedTraceOptions_673_; lean_object* v___x_674_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_toCold_664_ = lean_ctor_get(v_a_521_, 0);
lean_inc_ref(v_toCold_664_);
v_currRecDepth_665_ = lean_ctor_get(v_a_521_, 1);
lean_inc(v_currRecDepth_665_);
v_ref_666_ = lean_ctor_get(v_a_521_, 2);
lean_inc(v_ref_666_);
v_optionFlags_667_ = lean_ctor_get_uint16(v_a_521_, sizeof(void*)*3);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*3 + 2);
v_checkDeprecated_669_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*3 + 3);
v_isRecordingDeps_670_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_521_);
v_options_671_ = lean_ctor_get(v_toCold_664_, 2);
lean_inc_ref(v_options_671_);
v_maxRecDepth_672_ = lean_ctor_get(v_toCold_664_, 3);
v_inheritedTraceOptions_673_ = lean_ctor_get(v_toCold_664_, 11);
lean_inc_ref(v_inheritedTraceOptions_673_);
v___x_674_ = lean_box(0);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_nat_dec_eq(v_maxRecDepth_672_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_eq(v_currRecDepth_665_, v_maxRecDepth_672_);
if (v___x_859_ == 0)
{
goto v___jp_816_;
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v_inheritedTraceOptions_673_);
lean_dec_ref(v_options_671_);
lean_dec(v_currRecDepth_665_);
lean_dec_ref(v_toCold_664_);
lean_dec_ref(v_c_512_);
v___x_860_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_666_);
return v___x_860_;
}
}
else
{
goto v___jp_816_;
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
v___jp_527_:
{
lean_object* v___x_535_; 
v___x_535_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec_ref(v___y_533_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref_known(v___x_535_, 1);
v___x_536_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_537_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_536_, v___y_529_, v___y_530_);
return v___x_537_;
}
else
{
lean_dec_ref(v___y_529_);
return v___x_535_;
}
}
v___jp_538_:
{
if (lean_obj_tag(v___y_560_) == 1)
{
lean_object* v_val_561_; lean_object* v_p_562_; 
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_548_);
v_val_561_ = lean_ctor_get(v___y_560_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v___y_560_, 1);
v_p_562_ = lean_ctor_get(v_val_561_, 1);
lean_inc_ref(v_p_562_);
if (lean_obj_tag(v_p_562_) == 1)
{
lean_object* v_d_563_; lean_object* v_k_564_; lean_object* v_p_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_618_; 
v_d_563_ = lean_ctor_get(v_val_561_, 0);
v_k_564_ = lean_ctor_get(v_p_562_, 0);
v_p_565_ = lean_ctor_get(v_p_562_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_p_562_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_p_562_, 1);
lean_dec(v_unused_619_);
v___x_567_ = v_p_562_;
v_isShared_568_ = v_isSharedCheck_618_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_p_565_);
lean_inc(v_k_564_);
lean_dec(v_p_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_618_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_snd_572_; lean_object* v_fst_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_617_; 
v___x_569_ = lean_int_mul(v___y_557_, v_d_563_);
v___x_570_ = lean_int_mul(v_k_564_, v___y_545_);
v___x_571_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_569_, v___x_570_);
lean_dec(v___x_570_);
lean_dec(v___x_569_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
v_fst_573_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_617_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_617_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snd_572_);
lean_inc(v_fst_573_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_617_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_616_; 
v_fst_577_ = lean_ctor_get(v_snd_572_, 0);
v_snd_578_ = lean_ctor_get(v_snd_572_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_572_);
if (v_isSharedCheck_616_ == 0)
{
v___x_580_ = v_snd_572_;
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_snd_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_582_ = lean_int_mul(v_fst_577_, v_d_563_);
lean_dec(v_fst_577_);
lean_inc_ref(v___y_540_);
v___x_583_ = l_Int_Internal_Linear_Poly_mul(v___y_540_, v___x_582_);
lean_dec(v___x_582_);
v___x_584_ = lean_int_mul(v_snd_578_, v___y_545_);
lean_dec(v_snd_578_);
lean_inc_ref(v_p_565_);
v___x_585_ = l_Int_Internal_Linear_Poly_mul(v_p_565_, v___x_584_);
lean_dec(v___x_584_);
v___x_586_ = lean_int_mul(v___y_545_, v_d_563_);
lean_dec(v___y_545_);
v___x_587_ = l_Int_Internal_Linear_Poly_combine(v___x_583_, v___x_585_);
lean_inc(v_fst_573_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 2, v___x_587_);
lean_ctor_set(v___x_567_, 1, v___y_559_);
lean_ctor_set(v___x_567_, 0, v_fst_573_);
v___x_589_ = v___x_567_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_fst_573_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___y_559_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v___x_587_);
v___x_589_ = v_reuseFailAlloc_615_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
lean_inc(v_val_561_);
lean_inc_ref(v___y_556_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 5);
lean_ctor_set(v___x_580_, 1, v_val_561_);
lean_ctor_set(v___x_580_, 0, v___y_556_);
v___x_591_ = v___x_580_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_val_561_);
v___x_591_ = v_reuseFailAlloc_614_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_586_);
lean_ctor_set(v___x_592_, 1, v___x_589_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
v___x_593_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_594_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_593_, v___y_549_, v___y_541_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_594_, 1);
lean_inc_ref(v___y_554_);
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_592_, v___y_541_, v___y_555_, v___y_550_, v___y_546_, v___y_551_, v___y_539_, v___y_544_, v___y_543_, v___y_554_, v___y_547_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec_ref_known(v___x_595_, 1);
v___x_596_ = l_Int_Internal_Linear_Poly_mul(v___y_540_, v_k_564_);
lean_dec(v_k_564_);
v___x_597_ = lean_int_neg(v___y_557_);
lean_dec(v___y_557_);
v___x_598_ = l_Int_Internal_Linear_Poly_mul(v_p_565_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = l_Int_Internal_Linear_Poly_combine(v___x_596_, v___x_598_);
lean_inc(v_val_561_);
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 6);
lean_ctor_set(v___x_575_, 1, v_val_561_);
lean_ctor_set(v___x_575_, 0, v___y_556_);
v___x_601_ = v___x_575_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_val_561_);
v___x_601_ = v_reuseFailAlloc_613_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v_val_561_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; lean_object* v_unused_611_; lean_object* v_unused_612_; 
v_unused_610_ = lean_ctor_get(v_val_561_, 2);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_val_561_, 1);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_val_561_, 0);
lean_dec(v_unused_612_);
v___x_603_ = v_val_561_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_val_561_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 2, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_599_);
lean_ctor_set(v___x_603_, 0, v_fst_573_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_fst_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v___x_601_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_c_512_ = v___x_606_;
v_a_513_ = v___y_541_;
v_a_514_ = v___y_555_;
v_a_515_ = v___y_550_;
v_a_516_ = v___y_546_;
v_a_517_ = v___y_551_;
v_a_518_ = v___y_539_;
v_a_519_ = v___y_544_;
v_a_520_ = v___y_543_;
v_a_521_ = v___y_554_;
v_a_522_ = v___y_547_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_575_);
lean_dec(v_fst_573_);
lean_dec_ref(v_p_565_);
lean_dec(v_k_564_);
lean_dec(v_val_561_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v___y_540_);
return v___x_595_;
}
}
else
{
lean_dec_ref_known(v___x_592_, 3);
lean_del_object(v___x_575_);
lean_dec(v_fst_573_);
lean_dec_ref(v_p_565_);
lean_dec(v_k_564_);
lean_dec(v_val_561_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v___y_540_);
return v___x_594_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v_p_562_);
lean_dec(v___y_559_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_540_);
v___x_620_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_561_, v___y_541_, v___y_555_, v___y_550_, v___y_546_, v___y_551_, v___y_539_, v___y_544_, v___y_543_, v___y_554_, v___y_547_);
lean_dec_ref(v___y_554_);
return v___x_620_;
}
}
else
{
lean_object* v_toCold_621_; lean_object* v_options_622_; uint8_t v_hasTrace_623_; 
lean_dec(v___y_560_);
lean_dec(v___y_559_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_540_);
v_toCold_621_ = lean_ctor_get(v___y_554_, 0);
v_options_622_ = lean_ctor_get(v_toCold_621_, 2);
v_hasTrace_623_ = lean_ctor_get_uint8(v_options_622_, sizeof(void*)*1);
if (v_hasTrace_623_ == 0)
{
lean_dec_ref(v___y_556_);
v___y_528_ = v___y_548_;
v___y_529_ = v___y_552_;
v___y_530_ = v___y_541_;
v___y_531_ = v___y_544_;
v___y_532_ = v___y_543_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_547_;
goto v___jp_527_;
}
else
{
lean_object* v_inheritedTraceOptions_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_inheritedTraceOptions_624_ = lean_ctor_get(v_toCold_621_, 11);
v___x_625_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_542_);
lean_inc_ref(v___y_558_);
lean_inc_ref(v___y_553_);
v___x_626_ = l_Lean_Name_mkStr4(v___y_553_, v___y_558_, v___y_542_, v___x_625_);
v___x_627_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_626_);
v___x_628_ = l_Lean_Name_append(v___x_627_, v___x_626_);
v___x_629_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_624_, v_options_622_, v___x_628_);
lean_dec(v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v___x_626_);
lean_dec_ref(v___y_556_);
v___y_528_ = v___y_548_;
v___y_529_ = v___y_552_;
v___y_530_ = v___y_541_;
v___y_531_ = v___y_544_;
v___y_532_ = v___y_543_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_547_;
goto v___jp_527_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_556_, v___y_541_, v___y_554_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_626_, v_a_631_, v___y_544_, v___y_543_, v___y_554_, v___y_547_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_dec_ref_known(v___x_632_, 1);
v___y_528_ = v___y_548_;
v___y_529_ = v___y_552_;
v___y_530_ = v___y_541_;
v___y_531_ = v___y_544_;
v___y_532_ = v___y_543_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_547_;
goto v___jp_527_;
}
else
{
lean_dec_ref(v___y_554_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_548_);
return v___x_632_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v___x_626_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_548_);
v_a_633_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_630_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
}
v___jp_641_:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___y_642_);
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_653_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec_ref(v___y_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_654_, 0);
lean_dec(v_unused_663_);
v___x_656_ = v___x_654_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_dec(v___x_654_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_box(0);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
return v___x_654_;
}
}
v___jp_675_:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_687_, v___y_695_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v_dvds_699_; lean_object* v_size_700_; uint8_t v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v_dvds_699_ = lean_ctor_get(v_a_698_, 5);
lean_inc_ref(v_dvds_699_);
lean_dec(v_a_698_);
v_size_700_ = lean_ctor_get(v_dvds_699_, 2);
v___x_701_ = lean_nat_dec_lt(v___y_685_, v_size_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec_ref(v_dvds_699_);
v___x_702_ = l_outOfBounds___redArg(v___x_674_);
v___y_539_ = v___y_692_;
v___y_540_ = v___y_677_;
v___y_541_ = v___y_687_;
v___y_542_ = v___y_678_;
v___y_543_ = v___y_694_;
v___y_544_ = v___y_693_;
v___y_545_ = v___y_679_;
v___y_546_ = v___y_690_;
v___y_547_ = v___y_696_;
v___y_548_ = v___y_681_;
v___y_549_ = v___y_683_;
v___y_550_ = v___y_689_;
v___y_551_ = v___y_691_;
v___y_552_ = v___y_686_;
v___y_553_ = v___y_676_;
v___y_554_ = v___y_695_;
v___y_555_ = v___y_688_;
v___y_556_ = v___y_680_;
v___y_557_ = v___y_682_;
v___y_558_ = v___y_684_;
v___y_559_ = v___y_685_;
v___y_560_ = v___x_702_;
goto v___jp_538_;
}
else
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PersistentArray_get_x21___redArg(v___x_674_, v_dvds_699_, v___y_685_);
lean_dec_ref(v_dvds_699_);
v___y_539_ = v___y_692_;
v___y_540_ = v___y_677_;
v___y_541_ = v___y_687_;
v___y_542_ = v___y_678_;
v___y_543_ = v___y_694_;
v___y_544_ = v___y_693_;
v___y_545_ = v___y_679_;
v___y_546_ = v___y_690_;
v___y_547_ = v___y_696_;
v___y_548_ = v___y_681_;
v___y_549_ = v___y_683_;
v___y_550_ = v___y_689_;
v___y_551_ = v___y_691_;
v___y_552_ = v___y_686_;
v___y_553_ = v___y_676_;
v___y_554_ = v___y_695_;
v___y_555_ = v___y_688_;
v___y_556_ = v___y_680_;
v___y_557_ = v___y_682_;
v___y_558_ = v___y_684_;
v___y_559_ = v___y_685_;
v___y_560_ = v___x_703_;
goto v___jp_538_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_677_);
v_a_704_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_697_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_697_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_512_);
lean_inc_ref(v___y_724_);
v___x_727_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_726_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v_d_730_; lean_object* v_p_731_; uint8_t v___x_732_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_a_728_);
v_d_730_ = lean_ctor_get(v___x_729_, 0);
v_p_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_d_730_);
v___x_732_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_730_, v_p_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v___x_729_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_735_ = lean_int_dec_eq(v_d_730_, v___x_734_);
if (v___x_735_ == 0)
{
if (lean_obj_tag(v_p_731_) == 1)
{
lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v_p_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
lean_inc_ref(v_p_731_);
lean_inc(v_d_730_);
v_k_736_ = lean_ctor_get(v_p_731_, 0);
lean_inc(v_k_736_);
v_v_737_ = lean_ctor_get(v_p_731_, 1);
lean_inc_n(v_v_737_, 3);
v_p_738_ = lean_ctor_get(v_p_731_, 2);
lean_inc_ref(v_p_738_);
lean_inc_ref_n(v___x_729_, 2);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_739_, 0, v___x_729_);
lean_closure_set(v___f_739_, 1, v_v_737_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_740_, 0, v_v_737_);
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v___x_729_, v___y_716_, v___y_724_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = 0;
v___x_744_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
v___x_745_ = l_Lean_instBEqLBool_beq(v___x_744_, v___x_743_);
if (v___x_745_ == 0)
{
v___y_676_ = v___y_713_;
v___y_677_ = v_p_738_;
v___y_678_ = v___y_714_;
v___y_679_ = v_d_730_;
v___y_680_ = v___x_729_;
v___y_681_ = v_p_731_;
v___y_682_ = v_k_736_;
v___y_683_ = v___f_740_;
v___y_684_ = v___y_715_;
v___y_685_ = v_v_737_;
v___y_686_ = v___f_739_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_717_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_719_;
v___y_691_ = v___y_720_;
v___y_692_ = v___y_721_;
v___y_693_ = v___y_722_;
v___y_694_ = v___y_723_;
v___y_695_ = v___y_724_;
v___y_696_ = v___y_725_;
goto v___jp_675_;
}
else
{
lean_object* v___x_746_; 
lean_inc(v_v_737_);
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_737_, v___y_716_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref_known(v___x_746_, 1);
v___y_676_ = v___y_713_;
v___y_677_ = v_p_738_;
v___y_678_ = v___y_714_;
v___y_679_ = v_d_730_;
v___y_680_ = v___x_729_;
v___y_681_ = v_p_731_;
v___y_682_ = v_k_736_;
v___y_683_ = v___f_740_;
v___y_684_ = v___y_715_;
v___y_685_ = v_v_737_;
v___y_686_ = v___f_739_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_717_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_719_;
v___y_691_ = v___y_720_;
v___y_692_ = v___y_721_;
v___y_693_ = v___y_722_;
v___y_694_ = v___y_723_;
v___y_695_ = v___y_724_;
v___y_696_ = v___y_725_;
goto v___jp_675_;
}
else
{
lean_dec_ref(v___f_740_);
lean_dec_ref(v___f_739_);
lean_dec_ref(v_p_738_);
lean_dec(v_v_737_);
lean_dec_ref_known(v_p_731_, 3);
lean_dec(v_k_736_);
lean_dec(v_d_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
return v___x_746_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v___f_740_);
lean_dec_ref(v___f_739_);
lean_dec_ref(v_p_738_);
lean_dec(v_v_737_);
lean_dec_ref_known(v_p_731_, 3);
lean_dec(v_k_736_);
lean_dec(v_d_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
v_a_747_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_741_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_741_);
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
else
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v___x_729_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
return v___x_755_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_inc_ref(v_p_731_);
v___x_756_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_729_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_p_731_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_inc(v___y_725_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v___y_716_);
v___x_758_ = lean_grind_cutsat_assert_eq(v___x_757_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_767_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_box(0);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
return v___x_758_;
}
}
}
else
{
lean_object* v_toCold_768_; lean_object* v_options_769_; uint8_t v_hasTrace_770_; 
v_toCold_768_ = lean_ctor_get(v___y_724_, 0);
v_options_769_ = lean_ctor_get(v_toCold_768_, 2);
v_hasTrace_770_ = lean_ctor_get_uint8(v_options_769_, sizeof(void*)*1);
if (v_hasTrace_770_ == 0)
{
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
goto v___jp_524_;
}
else
{
lean_object* v_inheritedTraceOptions_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_inheritedTraceOptions_771_ = lean_ctor_get(v_toCold_768_, 11);
v___x_772_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_715_);
lean_inc_ref(v___y_713_);
v___x_773_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_773_);
v___x_775_ = l_Lean_Name_append(v___x_774_, v___x_773_);
v___x_776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_771_, v_options_769_, v___x_775_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v___x_773_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
goto v___jp_524_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_729_, v___y_716_, v___y_724_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_773_, v_a_778_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_dec_ref_known(v___x_779_, 1);
goto v___jp_524_;
}
else
{
return v___x_779_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v___x_773_);
lean_dec_ref(v___y_724_);
v_a_780_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_777_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_777_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_788_; lean_object* v_options_789_; uint8_t v_hasTrace_790_; 
v_toCold_788_ = lean_ctor_get(v___y_724_, 0);
v_options_789_ = lean_ctor_get(v_toCold_788_, 2);
v_hasTrace_790_ = lean_ctor_get_uint8(v_options_789_, sizeof(void*)*1);
if (v_hasTrace_790_ == 0)
{
v___y_642_ = v___x_729_;
v___y_643_ = v___y_716_;
v___y_644_ = v___y_717_;
v___y_645_ = v___y_718_;
v___y_646_ = v___y_719_;
v___y_647_ = v___y_720_;
v___y_648_ = v___y_721_;
v___y_649_ = v___y_722_;
v___y_650_ = v___y_723_;
v___y_651_ = v___y_724_;
v___y_652_ = v___y_725_;
goto v___jp_641_;
}
else
{
lean_object* v_inheritedTraceOptions_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_inheritedTraceOptions_791_ = lean_ctor_get(v_toCold_788_, 11);
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_715_);
lean_inc_ref(v___y_713_);
v___x_793_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Name_append(v___x_794_, v___x_793_);
v___x_796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_791_, v_options_789_, v___x_795_);
lean_dec(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec(v___x_793_);
v___y_642_ = v___x_729_;
v___y_643_ = v___y_716_;
v___y_644_ = v___y_717_;
v___y_645_ = v___y_718_;
v___y_646_ = v___y_719_;
v___y_647_ = v___y_720_;
v___y_648_ = v___y_721_;
v___y_649_ = v___y_722_;
v___y_650_ = v___y_723_;
v___y_651_ = v___y_724_;
v___y_652_ = v___y_725_;
goto v___jp_641_;
}
else
{
lean_object* v___x_797_; 
lean_inc_ref(v___x_729_);
v___x_797_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_729_, v___y_716_, v___y_724_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_793_, v_a_798_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_dec_ref_known(v___x_799_, 1);
v___y_642_ = v___x_729_;
v___y_643_ = v___y_716_;
v___y_644_ = v___y_717_;
v___y_645_ = v___y_718_;
v___y_646_ = v___y_719_;
v___y_647_ = v___y_720_;
v___y_648_ = v___y_721_;
v___y_649_ = v___y_722_;
v___y_650_ = v___y_723_;
v___y_651_ = v___y_724_;
v___y_652_ = v___y_725_;
goto v___jp_641_;
}
else
{
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
return v___x_799_;
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v___x_793_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___y_724_);
v_a_800_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_797_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___y_724_);
v_a_808_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_727_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_727_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_currRecDepth_665_, v___x_817_);
lean_dec(v_currRecDepth_665_);
v___x_819_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_819_, 0, v_toCold_664_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
lean_ctor_set(v___x_819_, 2, v_ref_666_);
lean_ctor_set_uint16(v___x_819_, sizeof(void*)*3, v_optionFlags_667_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 2, v_suppressElabErrors_668_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 3, v_checkDeprecated_669_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 4, v_isRecordingDeps_670_);
v___x_820_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_513_, v___x_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_848_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_848_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_848_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_848_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
if (v___x_825_ == 0)
{
uint8_t v_hasTrace_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_823_);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_671_, sizeof(void*)*1);
v___x_827_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_826_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_673_);
lean_dec_ref(v_options_671_);
v___y_713_ = v___x_827_;
v___y_714_ = v___x_829_;
v___y_715_ = v___x_828_;
v___y_716_ = v_a_513_;
v___y_717_ = v_a_514_;
v___y_718_ = v_a_515_;
v___y_719_ = v_a_516_;
v___y_720_ = v_a_517_;
v___y_721_ = v_a_518_;
v___y_722_ = v_a_519_;
v___y_723_ = v_a_520_;
v___y_724_ = v___x_819_;
v___y_725_ = v_a_522_;
goto v___jp_712_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_831_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_673_, v_options_671_, v___x_831_);
lean_dec_ref(v_options_671_);
lean_dec_ref(v_inheritedTraceOptions_673_);
if (v___x_832_ == 0)
{
v___y_713_ = v___x_827_;
v___y_714_ = v___x_829_;
v___y_715_ = v___x_828_;
v___y_716_ = v_a_513_;
v___y_717_ = v_a_514_;
v___y_718_ = v_a_515_;
v___y_719_ = v_a_516_;
v___y_720_ = v_a_517_;
v___y_721_ = v_a_518_;
v___y_722_ = v_a_519_;
v___y_723_ = v_a_520_;
v___y_724_ = v___x_819_;
v___y_725_ = v_a_522_;
goto v___jp_712_;
}
else
{
lean_object* v___x_833_; 
lean_inc_ref(v_c_512_);
v___x_833_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_512_, v_a_513_, v___x_819_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_830_, v_a_834_, v_a_519_, v_a_520_, v___x_819_, v_a_522_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec_ref_known(v___x_835_, 1);
v___y_713_ = v___x_827_;
v___y_714_ = v___x_829_;
v___y_715_ = v___x_828_;
v___y_716_ = v_a_513_;
v___y_717_ = v_a_514_;
v___y_718_ = v_a_515_;
v___y_719_ = v_a_516_;
v___y_720_ = v_a_517_;
v___y_721_ = v_a_518_;
v___y_722_ = v_a_519_;
v___y_723_ = v_a_520_;
v___y_724_ = v___x_819_;
v___y_725_ = v_a_522_;
goto v___jp_712_;
}
else
{
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_c_512_);
return v___x_835_;
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_c_512_);
v_a_836_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_833_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_833_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_inheritedTraceOptions_673_);
lean_dec_ref(v_options_671_);
lean_dec_ref(v_c_512_);
v___x_844_ = lean_box(0);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_844_);
v___x_846_ = v___x_823_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_inheritedTraceOptions_673_);
lean_dec_ref(v_options_671_);
lean_dec_ref(v_c_512_);
v_a_849_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_820_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_820_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec(v_a_862_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_d_886_; lean_object* v_p_887_; lean_object* v___x_888_; 
v_d_886_ = lean_ctor_get(v_c_874_, 0);
v_p_887_ = lean_ctor_get(v_c_874_, 1);
lean_inc_ref(v_p_887_);
v___x_888_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_887_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
if (lean_obj_tag(v_a_889_) == 1)
{
lean_object* v_val_890_; lean_object* v_snd_891_; lean_object* v_fst_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_inc(v_d_886_);
v_val_890_ = lean_ctor_get(v_a_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_a_889_, 1);
v_snd_891_ = lean_ctor_get(v_val_890_, 1);
lean_inc(v_snd_891_);
v_fst_892_ = lean_ctor_get(v_val_890_, 0);
lean_inc(v_fst_892_);
lean_dec(v_val_890_);
v_fst_893_ = lean_ctor_get(v_snd_891_, 0);
lean_inc(v_fst_893_);
v_snd_894_ = lean_ctor_get(v_snd_891_, 1);
lean_inc(v_snd_894_);
lean_dec(v_snd_891_);
v___x_895_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_895_, 0, v_c_874_);
lean_ctor_set(v___x_895_, 1, v_fst_892_);
lean_ctor_set(v___x_895_, 2, v_fst_893_);
v___x_896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_896_, 0, v_d_886_);
lean_ctor_set(v___x_896_, 1, v_snd_894_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
lean_inc_ref(v_a_883_);
v___x_897_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_896_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; 
lean_dec(v_a_889_);
lean_inc_ref(v_a_883_);
v___x_898_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_898_;
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_c_874_);
v_a_899_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_888_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_888_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec(v_a_908_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_box(0);
v___x_935_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_936_ = l_Lean_mkConst(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_958_; 
lean_inc_ref(v_e_940_);
v___x_958_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_940_, v_a_948_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_Lean_Expr_cleanupAnnotations(v_a_959_);
v___x_961_ = l_Lean_Expr_isApp(v___x_960_);
if (v___x_961_ == 0)
{
lean_dec_ref(v___x_960_);
lean_dec_ref(v_e_940_);
goto v___jp_952_;
}
else
{
lean_object* v_arg_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_arg_962_ = lean_ctor_get(v___x_960_, 1);
lean_inc_ref(v_arg_962_);
v___x_963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_960_);
v___x_964_ = l_Lean_Expr_isApp(v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v___x_963_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
goto v___jp_952_;
}
else
{
lean_object* v_arg_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_arg_965_ = lean_ctor_get(v___x_963_, 1);
lean_inc_ref(v_arg_965_);
v___x_966_ = l_Lean_Expr_appFnCleanup___redArg(v___x_963_);
v___x_967_ = l_Lean_Expr_isApp(v___x_966_);
if (v___x_967_ == 0)
{
lean_dec_ref(v___x_966_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
goto v___jp_952_;
}
else
{
lean_object* v_arg_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_arg_968_ = lean_ctor_get(v___x_966_, 1);
lean_inc_ref(v_arg_968_);
v___x_969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_966_);
v___x_970_ = l_Lean_Expr_isApp(v___x_969_);
if (v___x_970_ == 0)
{
lean_dec_ref(v___x_969_);
lean_dec_ref(v_arg_968_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
goto v___jp_952_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_969_);
v___x_972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_973_ = l_Lean_Expr_isConstOf(v___x_971_, v___x_972_);
lean_dec_ref(v___x_971_);
if (v___x_973_ == 0)
{
lean_dec_ref(v_arg_968_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
goto v___jp_952_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_968_, v_a_948_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1075_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1075_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1075_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___x_979_; 
v___x_979_ = lean_unbox(v_a_975_);
lean_dec(v_a_975_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v___x_980_ = lean_box(0);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_984_; 
lean_del_object(v___x_977_);
lean_inc_ref(v_arg_965_);
v___x_984_ = l_Lean_Meta_getIntValue_x3f(v_arg_965_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1051_; 
v_val_986_ = lean_ctor_get(v_a_985_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_988_ = v_a_985_;
v_isShared_989_ = v_isSharedCheck_1051_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_val_986_);
lean_dec(v_a_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1051_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; 
lean_inc_ref(v_e_940_);
v___x_990_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_940_, v_a_941_, v_a_945_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; uint8_t v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_del_object(v___x_988_);
lean_dec(v_val_986_);
lean_inc_ref(v_e_940_);
v___x_993_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_940_, v_a_941_, v_a_945_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1019_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1019_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1019_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v___x_999_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1003_; 
lean_del_object(v___x_996_);
lean_inc_ref(v_e_940_);
v___x_1003_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_1006_ = l_Lean_eagerReflBoolTrue;
v___x_1007_ = l_Lean_Meta_mkOfEqFalseCore(v_e_940_, v_a_1004_);
v___x_1008_ = l_Lean_mkApp4(v___x_1005_, v_arg_965_, v_arg_962_, v___x_1006_, v___x_1007_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Lean_Meta_Grind_pushNewFact(v___x_1008_, v___x_1009_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_1010_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v_a_1011_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1003_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1003_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v_a_1020_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_993_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_993_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_object* v___x_1028_; 
lean_dec_ref(v_arg_965_);
v___x_1028_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_962_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 0);
lean_ctor_set(v___x_988_, 0, v_e_940_);
v___x_1031_ = v___x_988_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_e_940_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1032_, 0, v_val_986_);
lean_ctor_set(v___x_1032_, 1, v_a_1029_);
lean_ctor_set(v___x_1032_, 2, v___x_1031_);
v___x_1033_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1032_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_1033_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_del_object(v___x_988_);
lean_dec(v_val_986_);
lean_dec_ref(v_e_940_);
v_a_1035_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1028_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1028_);
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
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_del_object(v___x_988_);
lean_dec(v_val_986_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v_a_1043_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_990_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_990_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_a_985_);
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
v___x_1052_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1053_ = l_Lean_indentExpr(v_e_940_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_945_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; uint8_t v_verbose_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v_verbose_1057_ = lean_ctor_get_uint8(v_a_1056_, 0);
lean_dec(v_a_1056_);
if (v_verbose_1057_ == 0)
{
lean_dec_ref_known(v___x_1054_, 2);
goto v___jp_955_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_Sym_reportIssue(v___x_1054_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_dec_ref_known(v___x_1058_, 1);
goto v___jp_955_;
}
else
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref_known(v___x_1054_, 2);
v_a_1059_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1055_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1055_);
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
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v_a_1067_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_984_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_984_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_arg_965_);
lean_dec_ref(v_arg_962_);
lean_dec_ref(v_e_940_);
v_a_1076_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_974_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_974_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
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
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_e_940_);
v_a_1084_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_958_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_958_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_box(0);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
v___jp_955_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_box(0);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec(v_a_1093_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1112_ = l_Lean_mkConst(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1121_ = l_Lean_mkConst(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
lean_inc_ref(v_e_1122_);
v___x_1140_ = l_Lean_Expr_cleanupAnnotations(v_e_1122_);
v___x_1141_ = l_Lean_Expr_isApp(v___x_1140_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_e_1122_);
goto v___jp_1134_;
}
else
{
lean_object* v_arg_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_arg_1142_ = lean_ctor_get(v___x_1140_, 1);
lean_inc_ref(v_arg_1142_);
v___x_1143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1140_);
v___x_1144_ = l_Lean_Expr_isApp(v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
goto v___jp_1134_;
}
else
{
lean_object* v_arg_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_arg_1145_ = lean_ctor_get(v___x_1143_, 1);
lean_inc_ref(v_arg_1145_);
v___x_1146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1143_);
v___x_1147_ = l_Lean_Expr_isApp(v___x_1146_);
if (v___x_1147_ == 0)
{
lean_dec_ref(v___x_1146_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
goto v___jp_1134_;
}
else
{
lean_object* v_arg_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_arg_1148_ = lean_ctor_get(v___x_1146_, 1);
lean_inc_ref(v_arg_1148_);
v___x_1149_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1146_);
v___x_1150_ = l_Lean_Expr_isApp(v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v___x_1149_);
lean_dec_ref(v_arg_1148_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
goto v___jp_1134_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1149_);
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1153_ = l_Lean_Expr_isConstOf(v___x_1151_, v___x_1152_);
lean_dec_ref(v___x_1151_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_arg_1148_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
goto v___jp_1134_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1148_, v_a_1130_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1286_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1286_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1286_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_unbox(v_a_1155_);
lean_dec(v_a_1155_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v___x_1160_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
lean_object* v___x_1164_; 
lean_del_object(v___x_1157_);
v___x_1164_ = l_Lean_Meta_getNatValue_x3f(v_arg_1145_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
if (lean_obj_tag(v_a_1165_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
v_val_1166_ = lean_ctor_get(v_a_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_a_1165_, 1);
lean_inc_ref(v_e_1122_);
v___x_1167_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1122_, v_a_1123_, v_a_1127_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; uint8_t v___x_1169_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_unbox(v_a_1168_);
lean_dec(v_a_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
lean_dec(v_val_1166_);
lean_inc_ref(v_e_1122_);
v___x_1170_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1122_, v_a_1123_, v_a_1127_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1195_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1195_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1195_;
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
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
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
lean_inc_ref(v_e_1122_);
v___x_1180_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1183_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1122_, v_a_1181_);
v___x_1184_ = l_Lean_mkApp3(v___x_1182_, v_arg_1145_, v_arg_1142_, v___x_1183_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = l_Lean_Meta_Grind_pushNewFact(v___x_1184_, v___x_1185_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1186_;
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1187_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1180_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1180_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1196_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1170_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1170_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v___x_1204_; 
lean_inc_ref(v_arg_1145_);
v___x_1204_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1145_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1208_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v_fst_1206_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_fst_1206_);
v_snd_1207_ = lean_ctor_get(v_a_1205_, 1);
lean_inc(v_snd_1207_);
lean_dec(v_a_1205_);
lean_inc_ref(v_arg_1142_);
v___x_1208_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1142_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1212_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v_fst_1210_ = lean_ctor_get(v_a_1209_, 0);
lean_inc(v_fst_1210_);
v_snd_1211_ = lean_ctor_get(v_a_1209_, 1);
lean_inc(v_snd_1211_);
lean_dec(v_a_1209_);
v___x_1212_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
lean_inc(v_fst_1210_);
v___x_1214_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1210_, v_a_1213_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Int_Internal_Linear_Expr_norm(v_a_1215_);
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1218_ = l_Lean_mkApp6(v___x_1217_, v_arg_1145_, v_arg_1142_, v_fst_1206_, v_fst_1210_, v_snd_1207_, v_snd_1211_);
lean_inc(v_val_1166_);
v___x_1219_ = lean_nat_to_int(v_val_1166_);
v___x_1220_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1220_, 0, v_e_1122_);
lean_ctor_set(v___x_1220_, 1, v___x_1218_);
lean_ctor_set(v___x_1220_, 2, v_val_1166_);
lean_ctor_set(v___x_1220_, 3, v_a_1215_);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1216_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
v___x_1222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1221_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1222_;
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_snd_1211_);
lean_dec(v_fst_1210_);
lean_dec(v_snd_1207_);
lean_dec(v_fst_1206_);
lean_dec(v_val_1166_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
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
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_snd_1211_);
lean_dec(v_fst_1210_);
lean_dec(v_snd_1207_);
lean_dec(v_fst_1206_);
lean_dec(v_val_1166_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1231_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1212_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1212_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_snd_1207_);
lean_dec(v_fst_1206_);
lean_dec(v_val_1166_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1239_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1208_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1208_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_val_1166_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1247_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1204_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1204_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_val_1166_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1255_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1167_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1167_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_a_1165_);
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1264_ = l_Lean_indentExpr(v_e_1122_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1127_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v_verbose_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_verbose_1268_ = lean_ctor_get_uint8(v_a_1267_, 0);
lean_dec(v_a_1267_);
if (v_verbose_1268_ == 0)
{
lean_dec_ref_known(v___x_1265_, 2);
goto v___jp_1137_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_Sym_reportIssue(v___x_1265_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_dec_ref_known(v___x_1269_, 1);
goto v___jp_1137_;
}
else
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v___x_1265_, 2);
v_a_1270_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1266_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1278_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1164_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1164_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_arg_1145_);
lean_dec_ref(v_arg_1142_);
lean_dec_ref(v_e_1122_);
v_a_1287_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1154_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1154_);
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
}
}
}
v___jp_1134_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec(v_a_1296_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1313_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1361_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1361_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1361_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
uint8_t v_lia_1330_; 
v_lia_1330_ = lean_ctor_get_uint8(v_a_1326_, sizeof(void*)*17 + 24);
lean_dec(v_a_1326_);
if (v_lia_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec_ref(v_e_1310_);
v___x_1331_ = lean_box(0);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1331_);
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v___x_1335_; 
lean_del_object(v___x_1328_);
lean_inc_ref(v_e_1310_);
v___x_1335_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1310_, v_a_1318_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l_Lean_Expr_cleanupAnnotations(v_a_1336_);
v___x_1338_ = l_Lean_Expr_isApp(v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_e_1310_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1337_);
v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_e_1310_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
v___x_1342_ = l_Lean_Expr_isApp(v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_e_1310_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1341_);
v___x_1344_ = l_Lean_Expr_isApp(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_e_1310_);
goto v___jp_1322_;
}
else
{
lean_object* v_arg_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_arg_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc_ref(v_arg_1345_);
v___x_1346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1343_);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1348_ = l_Lean_Expr_isConstOf(v___x_1346_, v___x_1347_);
lean_dec_ref(v___x_1346_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_e_1310_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1350_ = l_Lean_Expr_isConstOf(v_arg_1345_, v___x_1349_);
lean_dec_ref(v_arg_1345_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
return v___x_1352_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_e_1310_);
v_a_1353_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1335_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1335_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_e_1310_);
v_a_1362_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1325_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1325_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
v___jp_1322_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec(v_a_1371_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1385_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1386_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1384_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1388_;
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
