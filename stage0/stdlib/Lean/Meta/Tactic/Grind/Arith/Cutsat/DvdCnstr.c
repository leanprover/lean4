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
v___x_45_ = l_Int_Internal_Linear_Poly_getConst(v___y_43_);
v___x_46_ = lean_int_emod(v___x_45_, v___y_44_);
lean_dec(v___x_45_);
v___x_47_ = lean_int_dec_eq(v___x_46_, v___y_42_);
lean_dec(v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_41_);
v___x_48_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_40_);
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
v___x_52_ = l_Int_Internal_Linear_Poly_div(v___y_44_, v___y_43_);
lean_dec(v___y_44_);
v___x_53_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_53_, 0, v___y_40_);
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
lean_dec_ref(v___y_43_);
lean_dec(v___y_41_);
v___x_57_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_bmodCoeffs(v___y_40_);
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
v___y_40_ = v___y_59_;
v___y_41_ = v_d_60_;
v___y_42_ = v___x_63_;
v___y_43_ = v_p_61_;
v___y_44_ = v_g_62_;
goto v___jp_39_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_int_neg(v_g_62_);
lean_dec(v_g_62_);
v___y_40_ = v___y_59_;
v___y_41_ = v_d_60_;
v___y_42_ = v___x_63_;
v___y_43_ = v_p_61_;
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
lean_object* v_vars_432_; lean_object* v_varMap_433_; lean_object* v_varsHistory_434_; lean_object* v_natToIntMap_435_; lean_object* v_natDef_436_; lean_object* v_dvds_437_; lean_object* v_lowers_438_; lean_object* v_uppers_439_; lean_object* v_diseqs_440_; lean_object* v_elimEqs_441_; lean_object* v_active_442_; lean_object* v_elimStack_443_; lean_object* v_occurs_444_; lean_object* v_assignment_445_; lean_object* v_nextCnstrId_446_; uint8_t v_caseSplits_447_; lean_object* v_steps_448_; lean_object* v_penalties_449_; lean_object* v_numReorderRequests_450_; lean_object* v_conflict_x3f_451_; lean_object* v_diseqSplits_452_; lean_object* v_divMod_453_; uint8_t v_usedCommRing_454_; lean_object* v_nonlinearOccs_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
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
v_active_442_ = lean_ctor_get(v_s_431_, 10);
v_elimStack_443_ = lean_ctor_get(v_s_431_, 11);
v_occurs_444_ = lean_ctor_get(v_s_431_, 12);
v_assignment_445_ = lean_ctor_get(v_s_431_, 13);
v_nextCnstrId_446_ = lean_ctor_get(v_s_431_, 14);
v_caseSplits_447_ = lean_ctor_get_uint8(v_s_431_, sizeof(void*)*22);
v_steps_448_ = lean_ctor_get(v_s_431_, 15);
v_penalties_449_ = lean_ctor_get(v_s_431_, 16);
v_numReorderRequests_450_ = lean_ctor_get(v_s_431_, 17);
v_conflict_x3f_451_ = lean_ctor_get(v_s_431_, 18);
v_diseqSplits_452_ = lean_ctor_get(v_s_431_, 19);
v_divMod_453_ = lean_ctor_get(v_s_431_, 20);
v_usedCommRing_454_ = lean_ctor_get_uint8(v_s_431_, sizeof(void*)*22 + 1);
v_nonlinearOccs_455_ = lean_ctor_get(v_s_431_, 21);
v_isSharedCheck_464_ = !lean_is_exclusive(v_s_431_);
if (v_isSharedCheck_464_ == 0)
{
v___x_457_ = v_s_431_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_nonlinearOccs_455_);
lean_inc(v_divMod_453_);
lean_inc(v_diseqSplits_452_);
lean_inc(v_conflict_x3f_451_);
lean_inc(v_numReorderRequests_450_);
lean_inc(v_penalties_449_);
lean_inc(v_steps_448_);
lean_inc(v_nextCnstrId_446_);
lean_inc(v_assignment_445_);
lean_inc(v_occurs_444_);
lean_inc(v_elimStack_443_);
lean_inc(v_active_442_);
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
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_a_429_);
v___x_460_ = l_Lean_PersistentArray_set___redArg(v_dvds_437_, v_v_430_, v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 5, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_vars_432_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_varMap_433_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_varsHistory_434_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_natToIntMap_435_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_natDef_436_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_lowers_438_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_uppers_439_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_diseqs_440_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_elimEqs_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_active_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 11, v_elimStack_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 12, v_occurs_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 13, v_assignment_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 14, v_nextCnstrId_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 15, v_steps_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 16, v_penalties_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 17, v_numReorderRequests_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 18, v_conflict_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 19, v_diseqSplits_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 20, v_divMod_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 21, v_nonlinearOccs_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*22, v_caseSplits_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*22 + 1, v_usedCommRing_454_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_465_, lean_object* v_v_466_, lean_object* v_s_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_465_, v_v_466_, v_s_467_);
lean_dec(v_v_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_469_, lean_object* v_s_470_){
_start:
{
lean_object* v_vars_471_; lean_object* v_varMap_472_; lean_object* v_varsHistory_473_; lean_object* v_natToIntMap_474_; lean_object* v_natDef_475_; lean_object* v_dvds_476_; lean_object* v_lowers_477_; lean_object* v_uppers_478_; lean_object* v_diseqs_479_; lean_object* v_elimEqs_480_; lean_object* v_active_481_; lean_object* v_elimStack_482_; lean_object* v_occurs_483_; lean_object* v_assignment_484_; lean_object* v_nextCnstrId_485_; uint8_t v_caseSplits_486_; lean_object* v_steps_487_; lean_object* v_penalties_488_; lean_object* v_numReorderRequests_489_; lean_object* v_conflict_x3f_490_; lean_object* v_diseqSplits_491_; lean_object* v_divMod_492_; uint8_t v_usedCommRing_493_; lean_object* v_nonlinearOccs_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
v_vars_471_ = lean_ctor_get(v_s_470_, 0);
v_varMap_472_ = lean_ctor_get(v_s_470_, 1);
v_varsHistory_473_ = lean_ctor_get(v_s_470_, 2);
v_natToIntMap_474_ = lean_ctor_get(v_s_470_, 3);
v_natDef_475_ = lean_ctor_get(v_s_470_, 4);
v_dvds_476_ = lean_ctor_get(v_s_470_, 5);
v_lowers_477_ = lean_ctor_get(v_s_470_, 6);
v_uppers_478_ = lean_ctor_get(v_s_470_, 7);
v_diseqs_479_ = lean_ctor_get(v_s_470_, 8);
v_elimEqs_480_ = lean_ctor_get(v_s_470_, 9);
v_active_481_ = lean_ctor_get(v_s_470_, 10);
v_elimStack_482_ = lean_ctor_get(v_s_470_, 11);
v_occurs_483_ = lean_ctor_get(v_s_470_, 12);
v_assignment_484_ = lean_ctor_get(v_s_470_, 13);
v_nextCnstrId_485_ = lean_ctor_get(v_s_470_, 14);
v_caseSplits_486_ = lean_ctor_get_uint8(v_s_470_, sizeof(void*)*22);
v_steps_487_ = lean_ctor_get(v_s_470_, 15);
v_penalties_488_ = lean_ctor_get(v_s_470_, 16);
v_numReorderRequests_489_ = lean_ctor_get(v_s_470_, 17);
v_conflict_x3f_490_ = lean_ctor_get(v_s_470_, 18);
v_diseqSplits_491_ = lean_ctor_get(v_s_470_, 19);
v_divMod_492_ = lean_ctor_get(v_s_470_, 20);
v_usedCommRing_493_ = lean_ctor_get_uint8(v_s_470_, sizeof(void*)*22 + 1);
v_nonlinearOccs_494_ = lean_ctor_get(v_s_470_, 21);
v_isSharedCheck_503_ = !lean_is_exclusive(v_s_470_);
if (v_isSharedCheck_503_ == 0)
{
v___x_496_ = v_s_470_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_nonlinearOccs_494_);
lean_inc(v_divMod_492_);
lean_inc(v_diseqSplits_491_);
lean_inc(v_conflict_x3f_490_);
lean_inc(v_numReorderRequests_489_);
lean_inc(v_penalties_488_);
lean_inc(v_steps_487_);
lean_inc(v_nextCnstrId_485_);
lean_inc(v_assignment_484_);
lean_inc(v_occurs_483_);
lean_inc(v_elimStack_482_);
lean_inc(v_active_481_);
lean_inc(v_elimEqs_480_);
lean_inc(v_diseqs_479_);
lean_inc(v_uppers_478_);
lean_inc(v_lowers_477_);
lean_inc(v_dvds_476_);
lean_inc(v_natDef_475_);
lean_inc(v_natToIntMap_474_);
lean_inc(v_varsHistory_473_);
lean_inc(v_varMap_472_);
lean_inc(v_vars_471_);
lean_dec(v_s_470_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = lean_box(0);
v___x_499_ = l_Lean_PersistentArray_set___redArg(v_dvds_476_, v_v_469_, v___x_498_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 5, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_vars_471_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_varMap_472_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_varsHistory_473_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_natToIntMap_474_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_natDef_475_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_lowers_477_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_uppers_478_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_diseqs_479_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_elimEqs_480_);
lean_ctor_set(v_reuseFailAlloc_502_, 10, v_active_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 11, v_elimStack_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 12, v_occurs_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 13, v_assignment_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 14, v_nextCnstrId_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 15, v_steps_487_);
lean_ctor_set(v_reuseFailAlloc_502_, 16, v_penalties_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 17, v_numReorderRequests_489_);
lean_ctor_set(v_reuseFailAlloc_502_, 18, v_conflict_x3f_490_);
lean_ctor_set(v_reuseFailAlloc_502_, 19, v_diseqSplits_491_);
lean_ctor_set(v_reuseFailAlloc_502_, 20, v_divMod_492_);
lean_ctor_set(v_reuseFailAlloc_502_, 21, v_nonlinearOccs_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*22, v_caseSplits_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*22 + 1, v_usedCommRing_493_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_504_, lean_object* v_s_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_504_, v_s_505_);
lean_dec(v_v_504_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_516_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_517_ = l_Lean_Name_append(v___x_516_, v___x_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v_toCold_683_; lean_object* v_currRecDepth_684_; lean_object* v_ref_685_; uint16_t v_optionFlags_686_; uint8_t v_suppressElabErrors_687_; uint8_t v_checkDeprecated_688_; uint8_t v_isRecordingDeps_689_; lean_object* v_options_690_; lean_object* v_maxRecDepth_691_; lean_object* v_inheritedTraceOptions_692_; lean_object* v___x_693_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_toCold_683_ = lean_ctor_get(v_a_527_, 0);
lean_inc_ref(v_toCold_683_);
v_currRecDepth_684_ = lean_ctor_get(v_a_527_, 1);
lean_inc(v_currRecDepth_684_);
v_ref_685_ = lean_ctor_get(v_a_527_, 2);
lean_inc(v_ref_685_);
v_optionFlags_686_ = lean_ctor_get_uint16(v_a_527_, sizeof(void*)*3);
v_suppressElabErrors_687_ = lean_ctor_get_uint8(v_a_527_, sizeof(void*)*3 + 2);
v_checkDeprecated_688_ = lean_ctor_get_uint8(v_a_527_, sizeof(void*)*3 + 3);
v_isRecordingDeps_689_ = lean_ctor_get_uint8(v_a_527_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_527_);
v_options_690_ = lean_ctor_get(v_toCold_683_, 2);
lean_inc_ref(v_options_690_);
v_maxRecDepth_691_ = lean_ctor_get(v_toCold_683_, 3);
v_inheritedTraceOptions_692_ = lean_ctor_get(v_toCold_683_, 11);
lean_inc_ref(v_inheritedTraceOptions_692_);
v___x_693_ = lean_box(0);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_nat_dec_eq(v_maxRecDepth_691_, v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = lean_nat_dec_eq(v_currRecDepth_684_, v_maxRecDepth_691_);
if (v___x_875_ == 0)
{
goto v___jp_832_;
}
else
{
lean_object* v___x_876_; 
lean_dec_ref(v_inheritedTraceOptions_692_);
lean_dec_ref(v_options_690_);
lean_dec(v_currRecDepth_684_);
lean_dec_ref(v_toCold_683_);
lean_dec_ref(v_c_518_);
v___x_876_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_685_);
return v___x_876_;
}
}
else
{
goto v___jp_832_;
}
v___jp_530_:
{
lean_object* v_p_538_; lean_object* v___x_539_; 
v_p_538_ = lean_ctor_get(v___y_532_, 1);
lean_inc_ref(v_p_538_);
lean_dec_ref(v___y_532_);
v___x_539_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_538_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec_ref(v___y_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec_ref_known(v___x_539_, 1);
v___x_540_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_540_, v___y_531_, v___y_533_);
return v___x_541_;
}
else
{
lean_dec_ref(v___y_531_);
return v___x_539_;
}
}
v___jp_542_:
{
if (lean_obj_tag(v___y_563_) == 1)
{
lean_object* v_val_564_; lean_object* v_p_565_; 
lean_dec(v___y_543_);
v_val_564_ = lean_ctor_get(v___y_563_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___y_563_, 1);
v_p_565_ = lean_ctor_get(v_val_564_, 1);
lean_inc_ref(v_p_565_);
if (lean_obj_tag(v_p_565_) == 1)
{
lean_object* v_d_566_; lean_object* v_k_567_; lean_object* v_p_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_623_; 
v_d_566_ = lean_ctor_get(v_val_564_, 0);
v_k_567_ = lean_ctor_get(v_p_565_, 0);
v_p_568_ = lean_ctor_get(v_p_565_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_p_565_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_p_565_, 1);
lean_dec(v_unused_624_);
v___x_570_ = v_p_565_;
v_isShared_571_ = v_isSharedCheck_623_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_p_568_);
lean_inc(v_k_567_);
lean_dec(v_p_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_623_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_snd_575_; lean_object* v_fst_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_622_; 
v___x_572_ = lean_int_mul(v___y_552_, v_d_566_);
v___x_573_ = lean_int_mul(v_k_567_, v___y_556_);
v___x_574_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_572_, v___x_573_);
lean_dec(v___x_573_);
lean_dec(v___x_572_);
v_snd_575_ = lean_ctor_get(v___x_574_, 1);
v_fst_576_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_622_ == 0)
{
v___x_578_ = v___x_574_;
v_isShared_579_ = v_isSharedCheck_622_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_576_);
lean_dec(v___x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_622_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_621_; 
v_fst_580_ = lean_ctor_get(v_snd_575_, 0);
v_snd_581_ = lean_ctor_get(v_snd_575_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_snd_575_);
if (v_isSharedCheck_621_ == 0)
{
v___x_583_ = v_snd_575_;
v_isShared_584_ = v_isSharedCheck_621_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snd_581_);
lean_inc(v_fst_580_);
lean_dec(v_snd_575_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_621_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_585_ = lean_int_mul(v_fst_580_, v_d_566_);
lean_dec(v_fst_580_);
lean_inc_ref(v___y_550_);
v___x_586_ = l_Int_Internal_Linear_Poly_mul(v___y_550_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_int_mul(v_snd_581_, v___y_556_);
lean_dec(v_snd_581_);
lean_inc_ref(v_p_568_);
v___x_588_ = l_Int_Internal_Linear_Poly_mul(v_p_568_, v___x_587_);
lean_dec(v___x_587_);
v___x_589_ = lean_int_mul(v___y_556_, v_d_566_);
lean_dec(v___y_556_);
v___x_590_ = l_Int_Internal_Linear_Poly_combine(v___x_586_, v___x_588_);
lean_inc(v_fst_576_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_590_);
lean_ctor_set(v___x_570_, 1, v___y_562_);
lean_ctor_set(v___x_570_, 0, v_fst_576_);
v___x_592_ = v___x_570_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_fst_576_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___y_562_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___x_590_);
v___x_592_ = v_reuseFailAlloc_620_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
lean_inc(v_val_564_);
lean_inc_ref(v___y_555_);
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 5);
lean_ctor_set(v___x_583_, 1, v_val_564_);
lean_ctor_set(v___x_583_, 0, v___y_555_);
v___x_594_ = v___x_583_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___y_555_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_564_);
v___x_594_ = v_reuseFailAlloc_619_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_589_);
lean_ctor_set(v___x_596_, 1, v___x_592_);
lean_ctor_set(v___x_596_, 2, v___x_594_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
v___x_597_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_598_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_597_, v___y_551_, v___y_546_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; 
lean_dec_ref_known(v___x_598_, 1);
lean_inc_ref(v___y_558_);
v___x_599_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_596_, v___y_546_, v___y_553_, v___y_559_, v___y_549_, v___y_560_, v___y_557_, v___y_554_, v___y_547_, v___y_558_, v___y_544_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref_known(v___x_599_, 1);
v___x_600_ = l_Int_Internal_Linear_Poly_mul(v___y_550_, v_k_567_);
lean_dec(v_k_567_);
v___x_601_ = lean_int_neg(v___y_552_);
lean_dec(v___y_552_);
v___x_602_ = l_Int_Internal_Linear_Poly_mul(v_p_568_, v___x_601_);
lean_dec(v___x_601_);
v___x_603_ = l_Int_Internal_Linear_Poly_combine(v___x_600_, v___x_602_);
lean_inc(v_val_564_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 6);
lean_ctor_set(v___x_578_, 1, v_val_564_);
lean_ctor_set(v___x_578_, 0, v___y_555_);
v___x_605_ = v___x_578_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___y_555_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_val_564_);
v___x_605_ = v_reuseFailAlloc_618_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_isSharedCheck_613_ = !lean_is_exclusive(v_val_564_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_614_ = lean_ctor_get(v_val_564_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_val_564_, 2);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_val_564_, 1);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_val_564_, 0);
lean_dec(v_unused_617_);
v___x_607_ = v_val_564_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_val_564_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 3, v___x_595_);
lean_ctor_set(v___x_607_, 2, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_603_);
lean_ctor_set(v___x_607_, 0, v_fst_576_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_fst_576_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v___x_595_);
v___x_610_ = v_reuseFailAlloc_612_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
v_c_518_ = v___x_610_;
v_a_519_ = v___y_546_;
v_a_520_ = v___y_553_;
v_a_521_ = v___y_559_;
v_a_522_ = v___y_549_;
v_a_523_ = v___y_560_;
v_a_524_ = v___y_557_;
v_a_525_ = v___y_554_;
v_a_526_ = v___y_547_;
v_a_527_ = v___y_558_;
v_a_528_ = v___y_544_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_578_);
lean_dec(v_fst_576_);
lean_dec_ref(v_p_568_);
lean_dec(v_k_567_);
lean_dec(v_val_564_);
lean_dec_ref(v___y_558_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_550_);
return v___x_599_;
}
}
else
{
lean_dec_ref_known(v___x_596_, 4);
lean_del_object(v___x_578_);
lean_dec(v_fst_576_);
lean_dec_ref(v_p_568_);
lean_dec(v_k_567_);
lean_dec(v_val_564_);
lean_dec_ref(v___y_558_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_550_);
return v___x_598_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_625_; 
lean_dec_ref(v_p_565_);
lean_dec(v___y_562_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec_ref(v___y_550_);
v___x_625_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_564_, v___y_546_, v___y_553_, v___y_559_, v___y_549_, v___y_560_, v___y_557_, v___y_554_, v___y_547_, v___y_558_, v___y_544_);
lean_dec_ref(v___y_558_);
return v___x_625_;
}
}
else
{
lean_object* v___x_626_; 
lean_dec(v___y_563_);
lean_dec(v___y_562_);
lean_dec(v___y_556_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec_ref(v___y_550_);
v___x_626_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v___y_555_, v___y_546_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_toCold_627_; lean_object* v_options_628_; lean_object* v_a_629_; lean_object* v_inheritedTraceOptions_630_; uint8_t v_hasTrace_631_; lean_object* v___f_632_; 
v_toCold_627_ = lean_ctor_get(v___y_558_, 0);
v_options_628_ = lean_ctor_get(v_toCold_627_, 2);
v_a_629_ = lean_ctor_get(v___x_626_, 0);
lean_inc_n(v_a_629_, 2);
lean_dec_ref_known(v___x_626_, 1);
v_inheritedTraceOptions_630_ = lean_ctor_get(v_toCold_627_, 11);
v_hasTrace_631_ = lean_ctor_get_uint8(v_options_628_, sizeof(void*)*1);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_632_, 0, v_a_629_);
lean_closure_set(v___f_632_, 1, v___y_543_);
if (v_hasTrace_631_ == 0)
{
v___y_531_ = v___f_632_;
v___y_532_ = v_a_629_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_554_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_544_;
goto v___jp_530_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_561_);
lean_inc_ref(v___y_548_);
v___x_634_ = l_Lean_Name_mkStr4(v___y_548_, v___y_561_, v___y_545_, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_634_);
v___x_636_ = l_Lean_Name_append(v___x_635_, v___x_634_);
v___x_637_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_630_, v_options_628_, v___x_636_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
lean_dec(v___x_634_);
v___y_531_ = v___f_632_;
v___y_532_ = v_a_629_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_554_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_544_;
goto v___jp_530_;
}
else
{
lean_object* v___x_638_; 
lean_inc(v_a_629_);
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_629_, v___y_546_, v___y_558_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_634_, v_a_639_, v___y_554_, v___y_547_, v___y_558_, v___y_544_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
v___y_531_ = v___f_632_;
v___y_532_ = v_a_629_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_554_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_544_;
goto v___jp_530_;
}
else
{
lean_dec_ref(v___f_632_);
lean_dec(v_a_629_);
lean_dec_ref(v___y_558_);
return v___x_640_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_634_);
lean_dec_ref(v___f_632_);
lean_dec(v_a_629_);
lean_dec_ref(v___y_558_);
v_a_641_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_638_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___y_558_);
lean_dec(v___y_543_);
v_a_649_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_626_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_626_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
v___jp_657_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___y_658_);
v___x_670_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_669_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec_ref(v___y_667_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_679_);
v___x_672_ = v___x_670_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_670_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
return v___x_670_;
}
}
v___jp_680_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
v___jp_694_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_704_, v___y_712_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v_dvds_716_; lean_object* v_size_717_; uint8_t v___x_718_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v_dvds_716_ = lean_ctor_get(v_a_715_, 5);
lean_inc_ref(v_dvds_716_);
lean_dec(v_a_715_);
v_size_717_ = lean_ctor_get(v_dvds_716_, 2);
v___x_718_ = lean_nat_dec_lt(v___y_697_, v_size_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v_dvds_716_);
v___x_719_ = l_outOfBounds___redArg(v___x_693_);
lean_inc(v___y_697_);
v___y_543_ = v___y_697_;
v___y_544_ = v___y_713_;
v___y_545_ = v___y_698_;
v___y_546_ = v___y_704_;
v___y_547_ = v___y_711_;
v___y_548_ = v___y_701_;
v___y_549_ = v___y_707_;
v___y_550_ = v___y_695_;
v___y_551_ = v___y_702_;
v___y_552_ = v___y_696_;
v___y_553_ = v___y_705_;
v___y_554_ = v___y_710_;
v___y_555_ = v___y_699_;
v___y_556_ = v___y_700_;
v___y_557_ = v___y_709_;
v___y_558_ = v___y_712_;
v___y_559_ = v___y_706_;
v___y_560_ = v___y_708_;
v___y_561_ = v___y_703_;
v___y_562_ = v___y_697_;
v___y_563_ = v___x_719_;
goto v___jp_542_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentArray_get_x21___redArg(v___x_693_, v_dvds_716_, v___y_697_);
lean_dec_ref(v_dvds_716_);
lean_inc(v___y_697_);
v___y_543_ = v___y_697_;
v___y_544_ = v___y_713_;
v___y_545_ = v___y_698_;
v___y_546_ = v___y_704_;
v___y_547_ = v___y_711_;
v___y_548_ = v___y_701_;
v___y_549_ = v___y_707_;
v___y_550_ = v___y_695_;
v___y_551_ = v___y_702_;
v___y_552_ = v___y_696_;
v___y_553_ = v___y_705_;
v___y_554_ = v___y_710_;
v___y_555_ = v___y_699_;
v___y_556_ = v___y_700_;
v___y_557_ = v___y_709_;
v___y_558_ = v___y_712_;
v___y_559_ = v___y_706_;
v___y_560_ = v___y_708_;
v___y_561_ = v___y_703_;
v___y_562_ = v___y_697_;
v___y_563_ = v___x_720_;
goto v___jp_542_;
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
v_a_721_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_714_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_714_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_518_);
lean_inc_ref(v___y_741_);
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_743_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v_d_747_; lean_object* v_p_748_; uint8_t v___x_749_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_a_745_);
v_d_747_ = lean_ctor_get(v___x_746_, 0);
v_p_748_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_d_747_);
v___x_749_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_747_, v_p_748_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; 
v___x_750_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v___x_746_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_752_ = lean_int_dec_eq(v_d_747_, v___x_751_);
if (v___x_752_ == 0)
{
if (lean_obj_tag(v_p_748_) == 1)
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v_p_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
lean_inc(v_d_747_);
v_k_753_ = lean_ctor_get(v_p_748_, 0);
lean_inc(v_k_753_);
v_v_754_ = lean_ctor_get(v_p_748_, 1);
lean_inc_n(v_v_754_, 2);
v_p_755_ = lean_ctor_get(v_p_748_, 2);
lean_inc_ref(v_p_755_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_756_, 0, v_v_754_);
lean_inc_ref(v___x_746_);
v___x_757_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v___x_746_, v___y_733_, v___y_741_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; uint8_t v___x_759_; uint8_t v___x_760_; uint8_t v___x_761_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = 0;
v___x_760_ = lean_unbox(v_a_758_);
lean_dec(v_a_758_);
v___x_761_ = l_Lean_instBEqLBool_beq(v___x_760_, v___x_759_);
if (v___x_761_ == 0)
{
v___y_695_ = v_p_755_;
v___y_696_ = v_k_753_;
v___y_697_ = v_v_754_;
v___y_698_ = v___y_730_;
v___y_699_ = v___x_746_;
v___y_700_ = v_d_747_;
v___y_701_ = v___y_731_;
v___y_702_ = v___f_756_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_733_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_735_;
v___y_707_ = v___y_736_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_739_;
v___y_711_ = v___y_740_;
v___y_712_ = v___y_741_;
v___y_713_ = v___y_742_;
goto v___jp_694_;
}
else
{
lean_object* v___x_762_; 
lean_inc(v_v_754_);
v___x_762_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_754_, v___y_733_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref_known(v___x_762_, 1);
v___y_695_ = v_p_755_;
v___y_696_ = v_k_753_;
v___y_697_ = v_v_754_;
v___y_698_ = v___y_730_;
v___y_699_ = v___x_746_;
v___y_700_ = v_d_747_;
v___y_701_ = v___y_731_;
v___y_702_ = v___f_756_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_733_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_735_;
v___y_707_ = v___y_736_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_739_;
v___y_711_ = v___y_740_;
v___y_712_ = v___y_741_;
v___y_713_ = v___y_742_;
goto v___jp_694_;
}
else
{
lean_dec_ref(v___f_756_);
lean_dec_ref(v_p_755_);
lean_dec(v_v_754_);
lean_dec(v_k_753_);
lean_dec(v_d_747_);
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
return v___x_762_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___f_756_);
lean_dec_ref(v_p_755_);
lean_dec(v_v_754_);
lean_dec(v_k_753_);
lean_dec(v_d_747_);
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
v_a_763_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_757_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_757_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v___x_746_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec_ref(v___y_741_);
return v___x_771_;
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_inc_ref(v_p_748_);
v___x_772_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_746_);
v___x_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_773_, 0, v_p_748_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_ctor_set(v___x_773_, 2, v___x_693_);
lean_inc(v___y_742_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc(v___y_733_);
v___x_774_ = lean_grind_cutsat_assert_eq(v___x_773_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_783_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_box(0);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
return v___x_774_;
}
}
}
else
{
lean_object* v_toCold_784_; lean_object* v_options_785_; uint8_t v_hasTrace_786_; 
v_toCold_784_ = lean_ctor_get(v___y_741_, 0);
v_options_785_ = lean_ctor_get(v_toCold_784_, 2);
v_hasTrace_786_ = lean_ctor_get_uint8(v_options_785_, sizeof(void*)*1);
if (v_hasTrace_786_ == 0)
{
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
goto v___jp_680_;
}
else
{
lean_object* v_inheritedTraceOptions_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_inheritedTraceOptions_787_ = lean_ctor_get(v_toCold_784_, 11);
v___x_788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_730_);
lean_inc_ref(v___y_732_);
lean_inc_ref(v___y_731_);
v___x_789_ = l_Lean_Name_mkStr4(v___y_731_, v___y_732_, v___y_730_, v___x_788_);
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_789_);
v___x_791_ = l_Lean_Name_append(v___x_790_, v___x_789_);
v___x_792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_787_, v_options_785_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_dec(v___x_789_);
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
goto v___jp_680_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_746_, v___y_733_, v___y_741_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_789_, v_a_794_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec_ref(v___y_741_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
goto v___jp_680_;
}
else
{
return v___x_795_;
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v___x_789_);
lean_dec_ref(v___y_741_);
v_a_796_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_793_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_793_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_804_; lean_object* v_options_805_; uint8_t v_hasTrace_806_; 
v_toCold_804_ = lean_ctor_get(v___y_741_, 0);
v_options_805_ = lean_ctor_get(v_toCold_804_, 2);
v_hasTrace_806_ = lean_ctor_get_uint8(v_options_805_, sizeof(void*)*1);
if (v_hasTrace_806_ == 0)
{
v___y_658_ = v___x_746_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
v___y_667_ = v___y_741_;
v___y_668_ = v___y_742_;
goto v___jp_657_;
}
else
{
lean_object* v_inheritedTraceOptions_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_inheritedTraceOptions_807_ = lean_ctor_get(v_toCold_804_, 11);
v___x_808_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_730_);
lean_inc_ref(v___y_732_);
lean_inc_ref(v___y_731_);
v___x_809_ = l_Lean_Name_mkStr4(v___y_731_, v___y_732_, v___y_730_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_809_);
v___x_811_ = l_Lean_Name_append(v___x_810_, v___x_809_);
v___x_812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_805_, v___x_811_);
lean_dec(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec(v___x_809_);
v___y_658_ = v___x_746_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
v___y_667_ = v___y_741_;
v___y_668_ = v___y_742_;
goto v___jp_657_;
}
else
{
lean_object* v___x_813_; 
lean_inc_ref(v___x_746_);
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___x_746_, v___y_733_, v___y_741_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_809_, v_a_814_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref_known(v___x_815_, 1);
v___y_658_ = v___x_746_;
v___y_659_ = v___y_733_;
v___y_660_ = v___y_734_;
v___y_661_ = v___y_735_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_737_;
v___y_664_ = v___y_738_;
v___y_665_ = v___y_739_;
v___y_666_ = v___y_740_;
v___y_667_ = v___y_741_;
v___y_668_ = v___y_742_;
goto v___jp_657_;
}
else
{
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
return v___x_815_;
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v___x_809_);
lean_dec_ref(v___x_746_);
lean_dec_ref(v___y_741_);
v_a_816_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec_ref(v___y_741_);
v_a_824_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_744_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_744_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_currRecDepth_684_, v___x_833_);
lean_dec(v_currRecDepth_684_);
v___x_835_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_835_, 0, v_toCold_683_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
lean_ctor_set(v___x_835_, 2, v_ref_685_);
lean_ctor_set_uint16(v___x_835_, sizeof(void*)*3, v_optionFlags_686_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*3 + 2, v_suppressElabErrors_687_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*3 + 3, v_checkDeprecated_688_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*3 + 4, v_isRecordingDeps_689_);
v___x_836_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_519_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_864_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_864_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_864_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_864_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; 
v___x_841_ = lean_unbox(v_a_837_);
lean_dec(v_a_837_);
if (v___x_841_ == 0)
{
uint8_t v_hasTrace_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_839_);
v_hasTrace_842_ = lean_ctor_get_uint8(v_options_690_, sizeof(void*)*1);
v___x_843_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_844_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_845_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_842_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_692_);
lean_dec_ref(v_options_690_);
v___y_730_ = v___x_845_;
v___y_731_ = v___x_843_;
v___y_732_ = v___x_844_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v_a_525_;
v___y_740_ = v_a_526_;
v___y_741_ = v___x_835_;
v___y_742_ = v_a_528_;
goto v___jp_729_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_846_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_847_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_848_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_692_, v_options_690_, v___x_847_);
lean_dec_ref(v_options_690_);
lean_dec_ref(v_inheritedTraceOptions_692_);
if (v___x_848_ == 0)
{
v___y_730_ = v___x_845_;
v___y_731_ = v___x_843_;
v___y_732_ = v___x_844_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v_a_525_;
v___y_740_ = v_a_526_;
v___y_741_ = v___x_835_;
v___y_742_ = v_a_528_;
goto v___jp_729_;
}
else
{
lean_object* v___x_849_; 
lean_inc_ref(v_c_518_);
v___x_849_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_518_, v_a_519_, v___x_835_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_846_, v_a_850_, v_a_525_, v_a_526_, v___x_835_, v_a_528_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref_known(v___x_851_, 1);
v___y_730_ = v___x_845_;
v___y_731_ = v___x_843_;
v___y_732_ = v___x_844_;
v___y_733_ = v_a_519_;
v___y_734_ = v_a_520_;
v___y_735_ = v_a_521_;
v___y_736_ = v_a_522_;
v___y_737_ = v_a_523_;
v___y_738_ = v_a_524_;
v___y_739_ = v_a_525_;
v___y_740_ = v_a_526_;
v___y_741_ = v___x_835_;
v___y_742_ = v_a_528_;
goto v___jp_729_;
}
else
{
lean_dec_ref_known(v___x_835_, 3);
lean_dec_ref(v_c_518_);
return v___x_851_;
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref_known(v___x_835_, 3);
lean_dec_ref(v_c_518_);
v_a_852_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_849_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec_ref_known(v___x_835_, 3);
lean_dec_ref(v_inheritedTraceOptions_692_);
lean_dec_ref(v_options_690_);
lean_dec_ref(v_c_518_);
v___x_860_ = lean_box(0);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_860_);
v___x_862_ = v___x_839_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref_known(v___x_835_, 3);
lean_dec_ref(v_inheritedTraceOptions_692_);
lean_dec_ref(v_options_690_);
lean_dec_ref(v_c_518_);
v_a_865_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_836_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_836_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec(v_a_878_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_d_902_; lean_object* v_p_903_; lean_object* v___x_904_; 
v_d_902_ = lean_ctor_get(v_c_890_, 0);
v_p_903_ = lean_ctor_get(v_c_890_, 1);
lean_inc_ref(v_p_903_);
v___x_904_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_903_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
if (lean_obj_tag(v_a_905_) == 1)
{
lean_object* v_val_906_; lean_object* v_snd_907_; lean_object* v_fst_908_; lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_inc(v_d_902_);
v_val_906_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_a_905_, 1);
v_snd_907_ = lean_ctor_get(v_val_906_, 1);
lean_inc(v_snd_907_);
v_fst_908_ = lean_ctor_get(v_val_906_, 0);
lean_inc(v_fst_908_);
lean_dec(v_val_906_);
v_fst_909_ = lean_ctor_get(v_snd_907_, 0);
lean_inc(v_fst_909_);
v_snd_910_ = lean_ctor_get(v_snd_907_, 1);
lean_inc(v_snd_910_);
lean_dec(v_snd_907_);
v___x_911_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_911_, 0, v_c_890_);
lean_ctor_set(v___x_911_, 1, v_fst_908_);
lean_ctor_set(v___x_911_, 2, v_fst_909_);
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_913_, 0, v_d_902_);
lean_ctor_set(v___x_913_, 1, v_snd_910_);
lean_ctor_set(v___x_913_, 2, v___x_911_);
lean_ctor_set(v___x_913_, 3, v___x_912_);
lean_inc_ref(v_a_899_);
v___x_914_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_913_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; 
lean_dec(v_a_905_);
lean_inc_ref(v_a_899_);
v___x_915_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_915_;
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_c_890_);
v_a_916_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_904_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_904_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec(v_a_925_);
return v_res_936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_953_ = l_Lean_mkConst(v___x_952_, v___x_951_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_975_; 
lean_inc_ref(v_e_957_);
v___x_975_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_957_, v_a_965_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Expr_cleanupAnnotations(v_a_976_);
lean_dec(v_a_976_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_dec_ref(v___x_977_);
lean_dec_ref(v_e_957_);
goto v___jp_969_;
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
lean_dec_ref(v_e_957_);
goto v___jp_969_;
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
lean_dec_ref(v_e_957_);
goto v___jp_969_;
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_981_);
v___x_984_ = l_Lean_Expr_isApp(v___x_983_);
if (v___x_984_ == 0)
{
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v_e_957_);
goto v___jp_969_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_983_);
lean_dec_ref(v___x_983_);
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_987_ = l_Lean_Expr_isConstOf(v___x_985_, v___x_986_);
lean_dec_ref(v___x_985_);
if (v___x_987_ == 0)
{
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v_e_957_);
goto v___jp_969_;
}
else
{
lean_object* v_arg_988_; lean_object* v_arg_989_; lean_object* v_arg_990_; lean_object* v___x_991_; 
v_arg_988_ = lean_ctor_get(v___x_977_, 1);
lean_inc_ref(v_arg_988_);
lean_dec_ref(v___x_977_);
v_arg_989_ = lean_ctor_get(v___x_979_, 1);
lean_inc_ref(v_arg_989_);
lean_dec_ref(v___x_979_);
v_arg_990_ = lean_ctor_get(v___x_981_, 1);
lean_inc_ref(v_arg_990_);
lean_dec_ref(v___x_981_);
v___x_991_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_990_, v_a_965_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1093_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1093_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1093_;
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
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
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
lean_inc_ref(v_arg_989_);
v___x_1001_ = l_Lean_Meta_getIntValue_x3f(v_arg_989_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
if (lean_obj_tag(v_a_1002_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1069_; 
v_val_1003_ = lean_ctor_get(v_a_1002_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_a_1002_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1005_ = v_a_1002_;
v_isShared_1006_ = v_isSharedCheck_1069_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_val_1003_);
lean_dec(v_a_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1069_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; 
lean_inc_ref(v_e_957_);
v___x_1007_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_957_, v_a_958_, v_a_962_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; uint8_t v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_unbox(v_a_1008_);
lean_dec(v_a_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
lean_del_object(v___x_1005_);
lean_dec(v_val_1003_);
lean_inc_ref(v_e_957_);
v___x_1010_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_957_, v_a_958_, v_a_962_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1036_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1036_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1036_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_unbox(v_a_1011_);
lean_dec(v_a_1011_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v___x_1016_ = lean_box(0);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1016_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
else
{
lean_object* v___x_1020_; 
lean_del_object(v___x_1013_);
lean_inc_ref(v_e_957_);
v___x_1020_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_1023_ = l_Lean_eagerReflBoolTrue;
v___x_1024_ = l_Lean_Meta_mkOfEqFalseCore(v_e_957_, v_a_1021_);
v___x_1025_ = l_Lean_mkApp4(v___x_1022_, v_arg_989_, v_arg_988_, v___x_1023_, v___x_1024_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = l_Lean_Meta_Grind_pushNewFact(v___x_1025_, v___x_1026_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_1027_;
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v_a_1028_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1020_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1020_);
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
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v_a_1037_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1010_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1010_);
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
else
{
lean_object* v___x_1045_; 
lean_dec_ref(v_arg_989_);
v___x_1045_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_988_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
lean_ctor_set(v___x_1005_, 0, v_e_957_);
v___x_1048_ = v___x_1005_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_e_957_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1050_, 0, v_val_1003_);
lean_ctor_set(v___x_1050_, 1, v_a_1046_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set(v___x_1050_, 3, v___x_1049_);
v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1050_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_1051_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1005_);
lean_dec(v_val_1003_);
lean_dec_ref(v_e_957_);
v_a_1053_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1045_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1045_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_del_object(v___x_1005_);
lean_dec(v_val_1003_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v_a_1061_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1007_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1007_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_a_1002_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
v___x_1070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1071_ = l_Lean_indentExpr(v_e_957_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_962_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; uint8_t v_verbose_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_verbose_1075_ = lean_ctor_get_uint8(v_a_1074_, 0);
lean_dec(v_a_1074_);
if (v_verbose_1075_ == 0)
{
lean_dec_ref_known(v___x_1072_, 2);
goto v___jp_972_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_Sym_reportIssue(v___x_1072_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_dec_ref_known(v___x_1076_, 1);
goto v___jp_972_;
}
else
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref_known(v___x_1072_, 2);
v_a_1077_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1073_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1073_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v_a_1085_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1001_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1001_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_arg_988_);
lean_dec_ref(v_e_957_);
v_a_1094_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_991_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_991_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
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
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v_e_957_);
v_a_1102_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_975_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_975_);
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
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_box(0);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
v___jp_972_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec(v_a_1111_);
return v_res_1122_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1130_ = l_Lean_mkConst(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1139_ = l_Lean_mkConst(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = l_Lean_Expr_cleanupAnnotations(v_e_1140_);
v___x_1159_ = l_Lean_Expr_isApp(v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_e_1140_);
goto v___jp_1152_;
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
lean_dec_ref(v_e_1140_);
goto v___jp_1152_;
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
lean_dec_ref(v_e_1140_);
goto v___jp_1152_;
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1162_);
v___x_1165_ = l_Lean_Expr_isApp(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec_ref(v___x_1164_);
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_e_1140_);
goto v___jp_1152_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1167_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1168_ = l_Lean_Expr_isConstOf(v___x_1166_, v___x_1167_);
lean_dec_ref(v___x_1166_);
if (v___x_1168_ == 0)
{
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_e_1140_);
goto v___jp_1152_;
}
else
{
lean_object* v_arg_1169_; lean_object* v_arg_1170_; lean_object* v_arg_1171_; lean_object* v___x_1172_; 
v_arg_1169_ = lean_ctor_get(v___x_1158_, 1);
lean_inc_ref(v_arg_1169_);
lean_dec_ref(v___x_1158_);
v_arg_1170_ = lean_ctor_get(v___x_1160_, 1);
lean_inc_ref(v_arg_1170_);
lean_dec_ref(v___x_1160_);
v_arg_1171_ = lean_ctor_get(v___x_1162_, 1);
lean_inc_ref(v_arg_1171_);
lean_dec_ref(v___x_1162_);
v___x_1172_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1171_, v_a_1148_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1305_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1305_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1305_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_unbox(v_a_1173_);
lean_dec(v_a_1173_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v___x_1178_ = lean_box(0);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
lean_object* v___x_1182_; 
lean_del_object(v___x_1175_);
v___x_1182_ = l_Lean_Meta_getNatValue_x3f(v_arg_1170_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
if (lean_obj_tag(v_a_1183_) == 1)
{
lean_object* v_val_1184_; lean_object* v___x_1185_; 
v_val_1184_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v_a_1183_, 1);
lean_inc_ref(v_e_1140_);
v___x_1185_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1140_, v_a_1141_, v_a_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; uint8_t v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_dec(v_val_1184_);
lean_inc_ref(v_e_1140_);
v___x_1188_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1140_, v_a_1141_, v_a_1145_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1213_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1213_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1213_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_unbox(v_a_1189_);
lean_dec(v_a_1189_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v___x_1194_ = lean_box(0);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
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
lean_object* v___x_1198_; 
lean_del_object(v___x_1191_);
lean_inc_ref(v_e_1140_);
v___x_1198_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1201_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1140_, v_a_1199_);
v___x_1202_ = l_Lean_mkApp3(v___x_1200_, v_arg_1170_, v_arg_1169_, v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = l_Lean_Meta_Grind_pushNewFact(v___x_1202_, v___x_1203_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1204_;
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1205_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1198_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1198_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1214_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1188_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1188_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v___x_1222_; 
lean_inc_ref(v_arg_1170_);
v___x_1222_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1170_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_fst_1224_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v_a_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_a_1223_);
lean_inc_ref(v_arg_1169_);
v___x_1226_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1169_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1230_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_fst_1228_);
v_snd_1229_ = lean_ctor_get(v_a_1227_, 1);
lean_inc(v_snd_1229_);
lean_dec(v_a_1227_);
v___x_1230_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
lean_inc(v_fst_1228_);
v___x_1232_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1228_, v_a_1231_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = l_Int_Internal_Linear_Expr_norm(v_a_1233_);
v___x_1235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1236_ = l_Lean_mkApp6(v___x_1235_, v_arg_1170_, v_arg_1169_, v_fst_1224_, v_fst_1228_, v_snd_1225_, v_snd_1229_);
lean_inc(v_val_1184_);
v___x_1237_ = lean_nat_to_int(v_val_1184_);
v___x_1238_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1238_, 0, v_e_1140_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
lean_ctor_set(v___x_1238_, 2, v_val_1184_);
lean_ctor_set(v___x_1238_, 3, v_a_1233_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1234_);
lean_ctor_set(v___x_1240_, 2, v___x_1238_);
lean_ctor_set(v___x_1240_, 3, v___x_1239_);
v___x_1241_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1240_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_snd_1229_);
lean_dec(v_fst_1228_);
lean_dec(v_snd_1225_);
lean_dec(v_fst_1224_);
lean_dec(v_val_1184_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1242_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1232_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1232_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_snd_1229_);
lean_dec(v_fst_1228_);
lean_dec(v_snd_1225_);
lean_dec(v_fst_1224_);
lean_dec(v_val_1184_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1250_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1230_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1230_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_snd_1225_);
lean_dec(v_fst_1224_);
lean_dec(v_val_1184_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1258_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1226_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1226_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_val_1184_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1266_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1222_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1222_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_val_1184_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1274_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1185_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1185_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_a_1183_);
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
v___x_1282_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1283_ = l_Lean_indentExpr(v_e_1140_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1145_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; uint8_t v_verbose_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v_verbose_1287_ = lean_ctor_get_uint8(v_a_1286_, 0);
lean_dec(v_a_1286_);
if (v_verbose_1287_ == 0)
{
lean_dec_ref_known(v___x_1284_, 2);
goto v___jp_1155_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Sym_reportIssue(v___x_1284_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_dec_ref_known(v___x_1288_, 1);
goto v___jp_1155_;
}
else
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref_known(v___x_1284_, 2);
v_a_1289_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1285_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
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
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1297_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1182_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1182_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_arg_1170_);
lean_dec_ref(v_arg_1169_);
lean_dec_ref(v_e_1140_);
v_a_1306_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1172_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1172_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec(v_a_1315_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1332_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1380_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1380_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1380_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v_lia_1349_; 
v_lia_1349_ = lean_ctor_get_uint8(v_a_1345_, sizeof(void*)*18 + 24);
lean_dec(v_a_1345_);
if (v_lia_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec_ref(v_e_1329_);
v___x_1350_ = lean_box(0);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v___x_1354_; 
lean_del_object(v___x_1347_);
lean_inc_ref(v_e_1329_);
v___x_1354_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1329_, v_a_1337_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = l_Lean_Expr_cleanupAnnotations(v_a_1355_);
lean_dec(v_a_1355_);
v___x_1357_ = l_Lean_Expr_isApp(v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec_ref(v___x_1356_);
lean_dec_ref(v_e_1329_);
goto v___jp_1341_;
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
lean_dec_ref(v_e_1329_);
goto v___jp_1341_;
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
lean_dec_ref(v_e_1329_);
goto v___jp_1341_;
}
else
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1363_ = l_Lean_Expr_isApp(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_e_1329_);
goto v___jp_1341_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1362_);
v___x_1365_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1366_ = l_Lean_Expr_isConstOf(v___x_1364_, v___x_1365_);
lean_dec_ref(v___x_1364_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_e_1329_);
goto v___jp_1341_;
}
else
{
lean_object* v_arg_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_arg_1367_ = lean_ctor_get(v___x_1362_, 1);
lean_inc_ref(v_arg_1367_);
lean_dec_ref(v___x_1362_);
v___x_1368_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1369_ = l_Lean_Expr_isConstOf(v_arg_1367_, v___x_1368_);
lean_dec_ref(v_arg_1367_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1371_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_e_1329_);
v_a_1372_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1354_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1354_);
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
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_e_1329_);
v_a_1381_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1344_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1344_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
v___jp_1341_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec(v_a_1390_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1404_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1405_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1407_;
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
