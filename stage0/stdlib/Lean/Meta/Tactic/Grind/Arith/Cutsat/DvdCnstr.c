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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 234, 237, 24, 129, 31, 246, 138)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "non-linear divisibility constraint found"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* v_c_5_){
_start:
{
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_9_; lean_object* v___y_10_; uint8_t v___y_11_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_28_; lean_object* v_d_29_; lean_object* v_p_30_; lean_object* v_d_35_; lean_object* v_p_36_; uint8_t v___x_37_; 
v_d_35_ = lean_ctor_get(v_c_5_, 0);
lean_inc(v_d_35_);
v_p_36_ = lean_ctor_get(v_c_5_, 1);
v___x_37_ = l_Int_Linear_Poly_isSorted(v_p_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc_ref(v_p_36_);
v___x_38_ = l_Int_Linear_Poly_norm(v_p_36_);
v___x_39_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_39_, 0, v_c_5_);
lean_inc_ref(v___x_38_);
lean_inc(v_d_35_);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v_d_35_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_39_);
v___y_28_ = v___x_40_;
v_d_29_ = v_d_35_;
v_p_30_ = v___x_38_;
goto v___jp_27_;
}
else
{
lean_inc_ref(v_p_36_);
v___y_28_ = v_c_5_;
v_d_29_ = v_d_35_;
v_p_30_ = v_p_36_;
goto v___jp_27_;
}
v___jp_6_:
{
if (v___y_11_ == 0)
{
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
return v___y_7_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_int_ediv(v___y_8_, v___y_10_);
lean_dec(v___y_8_);
v___x_13_ = l_Int_Linear_Poly_div(v___y_10_, v___y_9_);
lean_dec(v___y_10_);
v___x_14_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_14_, 0, v___y_7_);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v___x_12_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_14_);
return v___x_15_;
}
}
v___jp_16_:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = l_Int_Linear_Poly_getConst(v___y_20_);
v___x_23_ = lean_int_emod(v___x_22_, v___y_21_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_dec_eq(v___x_23_, v___y_17_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
v___y_7_ = v___y_18_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_20_;
v___y_10_ = v___y_21_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_26_ = lean_int_dec_eq(v___y_21_, v___x_25_);
if (v___x_26_ == 0)
{
v___y_7_ = v___y_18_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_20_;
v___y_10_ = v___y_21_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
return v___y_18_;
}
}
}
v___jp_27_:
{
lean_object* v_g_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_d_29_);
v_g_31_ = l_Int_Linear_Poly_gcdCoeffs(v_p_30_, v_d_29_);
v___x_32_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_33_ = lean_int_dec_lt(v_d_29_, v___x_32_);
if (v___x_33_ == 0)
{
v___y_17_ = v___x_32_;
v___y_18_ = v___y_28_;
v___y_19_ = v_d_29_;
v___y_20_ = v_p_30_;
v___y_21_ = v_g_31_;
goto v___jp_16_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_int_neg(v_g_31_);
lean_dec(v_g_31_);
v___y_17_ = v___x_32_;
v___y_18_ = v___y_28_;
v___y_19_ = v_d_29_;
v___y_20_ = v_p_30_;
v___y_21_ = v___x_34_;
goto v___jp_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v_env_48_; lean_object* v___x_49_; lean_object* v_mctx_50_; lean_object* v_lctx_51_; lean_object* v_options_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_47_ = lean_st_ref_get(v___y_45_);
v_env_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_env_48_);
lean_dec(v___x_47_);
v___x_49_ = lean_st_ref_get(v___y_43_);
v_mctx_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_mctx_50_);
lean_dec(v___x_49_);
v_lctx_51_ = lean_ctor_get(v___y_42_, 2);
v_options_52_ = lean_ctor_get(v___y_44_, 2);
lean_inc_ref(v_options_52_);
lean_inc_ref(v_lctx_51_);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v_env_48_);
lean_ctor_set(v___x_53_, 1, v_mctx_50_);
lean_ctor_set(v___x_53_, 2, v_lctx_51_);
lean_ctor_set(v___x_53_, 3, v_options_52_);
v___x_54_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_msgData_41_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_62_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_63_; double v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_float_of_nat(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_68_, lean_object* v_msg_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_121_; 
v_ref_75_ = lean_ctor_get(v___y_72_, 5);
v___x_76_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_121_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_121_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_121_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v_traceState_82_; lean_object* v_env_83_; lean_object* v_nextMacroScope_84_; lean_object* v_ngen_85_; lean_object* v_auxDeclNGen_86_; lean_object* v_cache_87_; lean_object* v_messages_88_; lean_object* v_infoState_89_; lean_object* v_snapshotTasks_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_120_; 
v___x_81_ = lean_st_ref_take(v___y_73_);
v_traceState_82_ = lean_ctor_get(v___x_81_, 4);
v_env_83_ = lean_ctor_get(v___x_81_, 0);
v_nextMacroScope_84_ = lean_ctor_get(v___x_81_, 1);
v_ngen_85_ = lean_ctor_get(v___x_81_, 2);
v_auxDeclNGen_86_ = lean_ctor_get(v___x_81_, 3);
v_cache_87_ = lean_ctor_get(v___x_81_, 5);
v_messages_88_ = lean_ctor_get(v___x_81_, 6);
v_infoState_89_ = lean_ctor_get(v___x_81_, 7);
v_snapshotTasks_90_ = lean_ctor_get(v___x_81_, 8);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_120_ == 0)
{
v___x_92_ = v___x_81_;
v_isShared_93_ = v_isSharedCheck_120_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_snapshotTasks_90_);
lean_inc(v_infoState_89_);
lean_inc(v_messages_88_);
lean_inc(v_cache_87_);
lean_inc(v_traceState_82_);
lean_inc(v_auxDeclNGen_86_);
lean_inc(v_ngen_85_);
lean_inc(v_nextMacroScope_84_);
lean_inc(v_env_83_);
lean_dec(v___x_81_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_120_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint64_t v_tid_94_; lean_object* v_traces_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_119_; 
v_tid_94_ = lean_ctor_get_uint64(v_traceState_82_, sizeof(void*)*1);
v_traces_95_ = lean_ctor_get(v_traceState_82_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v_traceState_82_);
if (v_isSharedCheck_119_ == 0)
{
v___x_97_ = v_traceState_82_;
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_traces_95_);
lean_dec(v_traceState_82_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; double v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_99_ = lean_box(0);
v___x_100_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_101_ = 0;
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_103_, 0, v_cls_68_);
lean_ctor_set(v___x_103_, 1, v___x_99_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3, v___x_100_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3 + 8, v___x_100_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 16, v___x_101_);
v___x_104_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_105_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v_a_77_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_inc(v_ref_75_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_ref_75_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_PersistentArray_push___redArg(v_traces_95_, v___x_106_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_107_);
v___x_109_ = v___x_97_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_107_);
lean_ctor_set_uint64(v_reuseFailAlloc_118_, sizeof(void*)*1, v_tid_94_);
v___x_109_ = v_reuseFailAlloc_118_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_109_);
v___x_111_ = v___x_92_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_env_83_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_nextMacroScope_84_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_ngen_85_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_auxDeclNGen_86_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_117_, 5, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_117_, 6, v_messages_88_);
lean_ctor_set(v_reuseFailAlloc_117_, 7, v_infoState_89_);
lean_ctor_set(v_reuseFailAlloc_117_, 8, v_snapshotTasks_90_);
v___x_111_ = v_reuseFailAlloc_117_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_st_ref_set(v___y_73_, v___x_111_);
v___x_113_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_113_);
v___x_115_ = v___x_79_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_122_, v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_cls_142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_144_ = l_Lean_Name_append(v___x_143_, v_cls_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_148_, lean_object* v_x_149_, lean_object* v_c_u2081_150_, lean_object* v_b_151_, lean_object* v_c_u2082_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_options_164_; lean_object* v_p_165_; lean_object* v_d_166_; lean_object* v_p_167_; lean_object* v_inheritedTraceOptions_168_; uint8_t v_hasTrace_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_d_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_p_176_; 
v_options_164_ = lean_ctor_get(v_a_161_, 2);
v_p_165_ = lean_ctor_get(v_c_u2081_150_, 0);
v_d_166_ = lean_ctor_get(v_c_u2082_152_, 0);
v_p_167_ = lean_ctor_get(v_c_u2082_152_, 1);
v_inheritedTraceOptions_168_ = lean_ctor_get(v_a_161_, 13);
v_hasTrace_169_ = lean_ctor_get_uint8(v_options_164_, sizeof(void*)*1);
v___x_170_ = lean_int_mul(v_a_148_, v_d_166_);
v___x_171_ = lean_nat_abs(v___x_170_);
lean_dec(v___x_170_);
v_d_172_ = lean_nat_to_int(v___x_171_);
lean_inc_ref(v_p_167_);
v___x_173_ = l_Int_Linear_Poly_mul(v_p_167_, v_a_148_);
v___x_174_ = lean_int_neg(v_b_151_);
lean_inc_ref(v_p_165_);
v___x_175_ = l_Int_Linear_Poly_mul(v_p_165_, v___x_174_);
lean_dec(v___x_174_);
v_p_176_ = l_Int_Linear_Poly_combine(v___x_173_, v___x_175_);
if (v_hasTrace_169_ == 0)
{
goto v___jp_177_;
}
else
{
lean_object* v_cls_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_cls_181_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_182_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_168_, v_options_164_, v___x_182_);
if (v___x_183_ == 0)
{
goto v___jp_177_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_149_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref(v___x_184_);
lean_inc_ref(v_c_u2081_150_);
v___x_186_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_150_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref(v___x_186_);
lean_inc_ref(v_c_u2082_152_);
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_152_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
v___x_190_ = l_Lean_MessageData_ofExpr(v_a_185_);
v___x_191_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_a_187_);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_191_);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_189_);
v___x_196_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_181_, v___x_195_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_dec_ref(v___x_196_);
goto v___jp_177_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
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
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_a_187_);
lean_dec(v_a_185_);
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_205_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_188_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_188_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_185_);
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_213_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_186_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_186_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_221_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_184_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_184_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
v___jp_177_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_178_, 0, v_x_149_);
lean_ctor_set(v___x_178_, 1, v_c_u2081_150_);
lean_ctor_set(v___x_178_, 2, v_c_u2082_152_);
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v_d_172_);
lean_ctor_set(v___x_179_, 1, v_p_176_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v_c_u2081_231_, lean_object* v_b_232_, lean_object* v_c_u2082_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_229_, v_x_230_, v_c_u2081_231_, v_b_232_, v_c_u2082_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_a_234_);
lean_dec(v_b_232_);
lean_dec(v_a_229_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_246_, v_msg_247_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_260_, v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec(v___y_262_);
return v_res_273_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = l_Lean_maxRecDepthErrorMessage;
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_284_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_285_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_ref_286_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_294_, lean_object* v_ref_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_295_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_308_, lean_object* v_ref_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_308_, v_ref_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec(v___y_310_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_p_334_; lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_options_337_; lean_object* v_currRecDepth_338_; lean_object* v_maxRecDepth_339_; lean_object* v_ref_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_initHeartbeats_343_; lean_object* v_maxHeartbeats_344_; lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; uint8_t v_diag_347_; lean_object* v_cancelTk_x3f_348_; uint8_t v_suppressElabErrors_349_; lean_object* v_inheritedTraceOptions_350_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_p_334_ = lean_ctor_get(v_c_322_, 1);
v_fileName_335_ = lean_ctor_get(v_a_331_, 0);
lean_inc_ref(v_fileName_335_);
v_fileMap_336_ = lean_ctor_get(v_a_331_, 1);
lean_inc_ref(v_fileMap_336_);
v_options_337_ = lean_ctor_get(v_a_331_, 2);
lean_inc_ref(v_options_337_);
v_currRecDepth_338_ = lean_ctor_get(v_a_331_, 3);
lean_inc(v_currRecDepth_338_);
v_maxRecDepth_339_ = lean_ctor_get(v_a_331_, 4);
lean_inc(v_maxRecDepth_339_);
v_ref_340_ = lean_ctor_get(v_a_331_, 5);
lean_inc(v_ref_340_);
v_currNamespace_341_ = lean_ctor_get(v_a_331_, 6);
lean_inc(v_currNamespace_341_);
v_openDecls_342_ = lean_ctor_get(v_a_331_, 7);
lean_inc(v_openDecls_342_);
v_initHeartbeats_343_ = lean_ctor_get(v_a_331_, 8);
lean_inc(v_initHeartbeats_343_);
v_maxHeartbeats_344_ = lean_ctor_get(v_a_331_, 9);
lean_inc(v_maxHeartbeats_344_);
v_quotContext_345_ = lean_ctor_get(v_a_331_, 10);
lean_inc(v_quotContext_345_);
v_currMacroScope_346_ = lean_ctor_get(v_a_331_, 11);
lean_inc(v_currMacroScope_346_);
v_diag_347_ = lean_ctor_get_uint8(v_a_331_, sizeof(void*)*14);
v_cancelTk_x3f_348_ = lean_ctor_get(v_a_331_, 12);
lean_inc(v_cancelTk_x3f_348_);
v_suppressElabErrors_349_ = lean_ctor_get_uint8(v_a_331_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_350_ = lean_ctor_get(v_a_331_, 13);
lean_inc_ref(v_inheritedTraceOptions_350_);
lean_dec_ref(v_a_331_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_nat_dec_eq(v_maxRecDepth_339_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_eq(v_currRecDepth_338_, v_maxRecDepth_339_);
if (v___x_384_ == 0)
{
goto v___jp_351_;
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v_inheritedTraceOptions_350_);
lean_dec(v_cancelTk_x3f_348_);
lean_dec(v_currMacroScope_346_);
lean_dec(v_quotContext_345_);
lean_dec(v_maxHeartbeats_344_);
lean_dec(v_initHeartbeats_343_);
lean_dec(v_openDecls_342_);
lean_dec(v_currNamespace_341_);
lean_dec(v_maxRecDepth_339_);
lean_dec(v_currRecDepth_338_);
lean_dec_ref(v_options_337_);
lean_dec_ref(v_fileMap_336_);
lean_dec_ref(v_fileName_335_);
lean_dec_ref(v_c_322_);
v___x_385_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_340_);
return v___x_385_;
}
}
else
{
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_currRecDepth_338_, v___x_352_);
lean_dec(v_currRecDepth_338_);
v___x_354_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_354_, 0, v_fileName_335_);
lean_ctor_set(v___x_354_, 1, v_fileMap_336_);
lean_ctor_set(v___x_354_, 2, v_options_337_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
lean_ctor_set(v___x_354_, 4, v_maxRecDepth_339_);
lean_ctor_set(v___x_354_, 5, v_ref_340_);
lean_ctor_set(v___x_354_, 6, v_currNamespace_341_);
lean_ctor_set(v___x_354_, 7, v_openDecls_342_);
lean_ctor_set(v___x_354_, 8, v_initHeartbeats_343_);
lean_ctor_set(v___x_354_, 9, v_maxHeartbeats_344_);
lean_ctor_set(v___x_354_, 10, v_quotContext_345_);
lean_ctor_set(v___x_354_, 11, v_currMacroScope_346_);
lean_ctor_set(v___x_354_, 12, v_cancelTk_x3f_348_);
lean_ctor_set(v___x_354_, 13, v_inheritedTraceOptions_350_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14, v_diag_347_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14 + 1, v_suppressElabErrors_349_);
lean_inc_ref(v_p_334_);
v___x_355_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_334_, v_a_323_, v___x_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_373_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_373_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_373_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
if (lean_obj_tag(v_a_356_) == 1)
{
lean_object* v_val_360_; lean_object* v_snd_361_; lean_object* v_snd_362_; lean_object* v_fst_363_; lean_object* v_fst_364_; lean_object* v_p_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_del_object(v___x_358_);
v_val_360_ = lean_ctor_get(v_a_356_, 0);
lean_inc(v_val_360_);
lean_dec_ref(v_a_356_);
v_snd_361_ = lean_ctor_get(v_val_360_, 1);
lean_inc(v_snd_361_);
v_snd_362_ = lean_ctor_get(v_snd_361_, 1);
lean_inc(v_snd_362_);
v_fst_363_ = lean_ctor_get(v_val_360_, 0);
lean_inc(v_fst_363_);
lean_dec(v_val_360_);
v_fst_364_ = lean_ctor_get(v_snd_361_, 0);
lean_inc(v_fst_364_);
lean_dec(v_snd_361_);
v_p_365_ = lean_ctor_get(v_snd_362_, 0);
v___x_366_ = l_Int_Linear_Poly_coeff(v_p_365_, v_fst_364_);
v___x_367_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_366_, v_fst_364_, v_snd_362_, v_fst_363_, v_c_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v___x_354_, v_a_332_);
lean_dec(v_fst_363_);
lean_dec(v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v___x_367_);
v_c_322_ = v_a_368_;
v_a_331_ = v___x_354_;
goto _start;
}
else
{
lean_dec_ref(v___x_354_);
return v___x_367_;
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_a_356_);
lean_dec_ref(v___x_354_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_c_322_);
v___x_371_ = v___x_358_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_c_322_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v___x_354_);
lean_dec_ref(v_c_322_);
v_a_374_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_355_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_355_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_399_, lean_object* v_v_400_, lean_object* v_s_401_){
_start:
{
lean_object* v_vars_402_; lean_object* v_varMap_403_; lean_object* v_vars_x27_404_; lean_object* v_varMap_x27_405_; lean_object* v_natToIntMap_406_; lean_object* v_natDef_407_; lean_object* v_dvds_408_; lean_object* v_lowers_409_; lean_object* v_uppers_410_; lean_object* v_diseqs_411_; lean_object* v_elimEqs_412_; lean_object* v_elimStack_413_; lean_object* v_occurs_414_; lean_object* v_assignment_415_; lean_object* v_nextCnstrId_416_; uint8_t v_caseSplits_417_; lean_object* v_conflict_x3f_418_; lean_object* v_diseqSplits_419_; lean_object* v_divMod_420_; lean_object* v_toIntIds_421_; lean_object* v_toIntInfos_422_; lean_object* v_toIntTermMap_423_; lean_object* v_toIntVarMap_424_; uint8_t v_usedCommRing_425_; lean_object* v_nonlinearOccs_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_435_; 
v_vars_402_ = lean_ctor_get(v_s_401_, 0);
v_varMap_403_ = lean_ctor_get(v_s_401_, 1);
v_vars_x27_404_ = lean_ctor_get(v_s_401_, 2);
v_varMap_x27_405_ = lean_ctor_get(v_s_401_, 3);
v_natToIntMap_406_ = lean_ctor_get(v_s_401_, 4);
v_natDef_407_ = lean_ctor_get(v_s_401_, 5);
v_dvds_408_ = lean_ctor_get(v_s_401_, 6);
v_lowers_409_ = lean_ctor_get(v_s_401_, 7);
v_uppers_410_ = lean_ctor_get(v_s_401_, 8);
v_diseqs_411_ = lean_ctor_get(v_s_401_, 9);
v_elimEqs_412_ = lean_ctor_get(v_s_401_, 10);
v_elimStack_413_ = lean_ctor_get(v_s_401_, 11);
v_occurs_414_ = lean_ctor_get(v_s_401_, 12);
v_assignment_415_ = lean_ctor_get(v_s_401_, 13);
v_nextCnstrId_416_ = lean_ctor_get(v_s_401_, 14);
v_caseSplits_417_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*23);
v_conflict_x3f_418_ = lean_ctor_get(v_s_401_, 15);
v_diseqSplits_419_ = lean_ctor_get(v_s_401_, 16);
v_divMod_420_ = lean_ctor_get(v_s_401_, 17);
v_toIntIds_421_ = lean_ctor_get(v_s_401_, 18);
v_toIntInfos_422_ = lean_ctor_get(v_s_401_, 19);
v_toIntTermMap_423_ = lean_ctor_get(v_s_401_, 20);
v_toIntVarMap_424_ = lean_ctor_get(v_s_401_, 21);
v_usedCommRing_425_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*23 + 1);
v_nonlinearOccs_426_ = lean_ctor_get(v_s_401_, 22);
v_isSharedCheck_435_ = !lean_is_exclusive(v_s_401_);
if (v_isSharedCheck_435_ == 0)
{
v___x_428_ = v_s_401_;
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_nonlinearOccs_426_);
lean_inc(v_toIntVarMap_424_);
lean_inc(v_toIntTermMap_423_);
lean_inc(v_toIntInfos_422_);
lean_inc(v_toIntIds_421_);
lean_inc(v_divMod_420_);
lean_inc(v_diseqSplits_419_);
lean_inc(v_conflict_x3f_418_);
lean_inc(v_nextCnstrId_416_);
lean_inc(v_assignment_415_);
lean_inc(v_occurs_414_);
lean_inc(v_elimStack_413_);
lean_inc(v_elimEqs_412_);
lean_inc(v_diseqs_411_);
lean_inc(v_uppers_410_);
lean_inc(v_lowers_409_);
lean_inc(v_dvds_408_);
lean_inc(v_natDef_407_);
lean_inc(v_natToIntMap_406_);
lean_inc(v_varMap_x27_405_);
lean_inc(v_vars_x27_404_);
lean_inc(v_varMap_403_);
lean_inc(v_vars_402_);
lean_dec(v_s_401_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_a_399_);
v___x_431_ = l_Lean_PersistentArray_set___redArg(v_dvds_408_, v_v_400_, v___x_430_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 6, v___x_431_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_vars_402_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_varMap_403_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_vars_x27_404_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_varMap_x27_405_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_natToIntMap_406_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v_natDef_407_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_lowers_409_);
lean_ctor_set(v_reuseFailAlloc_434_, 8, v_uppers_410_);
lean_ctor_set(v_reuseFailAlloc_434_, 9, v_diseqs_411_);
lean_ctor_set(v_reuseFailAlloc_434_, 10, v_elimEqs_412_);
lean_ctor_set(v_reuseFailAlloc_434_, 11, v_elimStack_413_);
lean_ctor_set(v_reuseFailAlloc_434_, 12, v_occurs_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 13, v_assignment_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 14, v_nextCnstrId_416_);
lean_ctor_set(v_reuseFailAlloc_434_, 15, v_conflict_x3f_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 16, v_diseqSplits_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 17, v_divMod_420_);
lean_ctor_set(v_reuseFailAlloc_434_, 18, v_toIntIds_421_);
lean_ctor_set(v_reuseFailAlloc_434_, 19, v_toIntInfos_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 20, v_toIntTermMap_423_);
lean_ctor_set(v_reuseFailAlloc_434_, 21, v_toIntVarMap_424_);
lean_ctor_set(v_reuseFailAlloc_434_, 22, v_nonlinearOccs_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*23, v_caseSplits_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*23 + 1, v_usedCommRing_425_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_436_, lean_object* v_v_437_, lean_object* v_s_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_436_, v_v_437_, v_s_438_);
lean_dec(v_v_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_440_, lean_object* v_s_441_){
_start:
{
lean_object* v_vars_442_; lean_object* v_varMap_443_; lean_object* v_vars_x27_444_; lean_object* v_varMap_x27_445_; lean_object* v_natToIntMap_446_; lean_object* v_natDef_447_; lean_object* v_dvds_448_; lean_object* v_lowers_449_; lean_object* v_uppers_450_; lean_object* v_diseqs_451_; lean_object* v_elimEqs_452_; lean_object* v_elimStack_453_; lean_object* v_occurs_454_; lean_object* v_assignment_455_; lean_object* v_nextCnstrId_456_; uint8_t v_caseSplits_457_; lean_object* v_conflict_x3f_458_; lean_object* v_diseqSplits_459_; lean_object* v_divMod_460_; lean_object* v_toIntIds_461_; lean_object* v_toIntInfos_462_; lean_object* v_toIntTermMap_463_; lean_object* v_toIntVarMap_464_; uint8_t v_usedCommRing_465_; lean_object* v_nonlinearOccs_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_vars_442_ = lean_ctor_get(v_s_441_, 0);
v_varMap_443_ = lean_ctor_get(v_s_441_, 1);
v_vars_x27_444_ = lean_ctor_get(v_s_441_, 2);
v_varMap_x27_445_ = lean_ctor_get(v_s_441_, 3);
v_natToIntMap_446_ = lean_ctor_get(v_s_441_, 4);
v_natDef_447_ = lean_ctor_get(v_s_441_, 5);
v_dvds_448_ = lean_ctor_get(v_s_441_, 6);
v_lowers_449_ = lean_ctor_get(v_s_441_, 7);
v_uppers_450_ = lean_ctor_get(v_s_441_, 8);
v_diseqs_451_ = lean_ctor_get(v_s_441_, 9);
v_elimEqs_452_ = lean_ctor_get(v_s_441_, 10);
v_elimStack_453_ = lean_ctor_get(v_s_441_, 11);
v_occurs_454_ = lean_ctor_get(v_s_441_, 12);
v_assignment_455_ = lean_ctor_get(v_s_441_, 13);
v_nextCnstrId_456_ = lean_ctor_get(v_s_441_, 14);
v_caseSplits_457_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*23);
v_conflict_x3f_458_ = lean_ctor_get(v_s_441_, 15);
v_diseqSplits_459_ = lean_ctor_get(v_s_441_, 16);
v_divMod_460_ = lean_ctor_get(v_s_441_, 17);
v_toIntIds_461_ = lean_ctor_get(v_s_441_, 18);
v_toIntInfos_462_ = lean_ctor_get(v_s_441_, 19);
v_toIntTermMap_463_ = lean_ctor_get(v_s_441_, 20);
v_toIntVarMap_464_ = lean_ctor_get(v_s_441_, 21);
v_usedCommRing_465_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*23 + 1);
v_nonlinearOccs_466_ = lean_ctor_get(v_s_441_, 22);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_441_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v_s_441_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_nonlinearOccs_466_);
lean_inc(v_toIntVarMap_464_);
lean_inc(v_toIntTermMap_463_);
lean_inc(v_toIntInfos_462_);
lean_inc(v_toIntIds_461_);
lean_inc(v_divMod_460_);
lean_inc(v_diseqSplits_459_);
lean_inc(v_conflict_x3f_458_);
lean_inc(v_nextCnstrId_456_);
lean_inc(v_assignment_455_);
lean_inc(v_occurs_454_);
lean_inc(v_elimStack_453_);
lean_inc(v_elimEqs_452_);
lean_inc(v_diseqs_451_);
lean_inc(v_uppers_450_);
lean_inc(v_lowers_449_);
lean_inc(v_dvds_448_);
lean_inc(v_natDef_447_);
lean_inc(v_natToIntMap_446_);
lean_inc(v_varMap_x27_445_);
lean_inc(v_vars_x27_444_);
lean_inc(v_varMap_443_);
lean_inc(v_vars_442_);
lean_dec(v_s_441_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_box(0);
v___x_471_ = l_Lean_PersistentArray_set___redArg(v_dvds_448_, v_v_440_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 6, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_vars_442_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_varMap_443_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_vars_x27_444_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_varMap_x27_445_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_natToIntMap_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_natDef_447_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_lowers_449_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_uppers_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_diseqs_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 10, v_elimEqs_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 11, v_elimStack_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 12, v_occurs_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 13, v_assignment_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 14, v_nextCnstrId_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 15, v_conflict_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 16, v_diseqSplits_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 17, v_divMod_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 18, v_toIntIds_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 19, v_toIntInfos_462_);
lean_ctor_set(v_reuseFailAlloc_474_, 20, v_toIntTermMap_463_);
lean_ctor_set(v_reuseFailAlloc_474_, 21, v_toIntVarMap_464_);
lean_ctor_set(v_reuseFailAlloc_474_, 22, v_nonlinearOccs_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*23, v_caseSplits_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*23 + 1, v_usedCommRing_465_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_476_, lean_object* v_s_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_476_, v_s_477_);
lean_dec(v_v_476_);
return v_res_478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_489_ = l_Lean_Name_append(v___x_488_, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v_fileName_766_; lean_object* v_fileMap_767_; lean_object* v_options_768_; lean_object* v_currRecDepth_769_; lean_object* v_maxRecDepth_770_; lean_object* v_ref_771_; lean_object* v_currNamespace_772_; lean_object* v_openDecls_773_; lean_object* v_initHeartbeats_774_; lean_object* v_maxHeartbeats_775_; lean_object* v_quotContext_776_; lean_object* v_currMacroScope_777_; uint8_t v_diag_778_; lean_object* v_cancelTk_x3f_779_; uint8_t v_suppressElabErrors_780_; lean_object* v_inheritedTraceOptions_781_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_fileName_766_ = lean_ctor_get(v_a_499_, 0);
lean_inc_ref(v_fileName_766_);
v_fileMap_767_ = lean_ctor_get(v_a_499_, 1);
lean_inc_ref(v_fileMap_767_);
v_options_768_ = lean_ctor_get(v_a_499_, 2);
lean_inc_ref(v_options_768_);
v_currRecDepth_769_ = lean_ctor_get(v_a_499_, 3);
lean_inc(v_currRecDepth_769_);
v_maxRecDepth_770_ = lean_ctor_get(v_a_499_, 4);
lean_inc(v_maxRecDepth_770_);
v_ref_771_ = lean_ctor_get(v_a_499_, 5);
lean_inc(v_ref_771_);
v_currNamespace_772_ = lean_ctor_get(v_a_499_, 6);
lean_inc(v_currNamespace_772_);
v_openDecls_773_ = lean_ctor_get(v_a_499_, 7);
lean_inc(v_openDecls_773_);
v_initHeartbeats_774_ = lean_ctor_get(v_a_499_, 8);
lean_inc(v_initHeartbeats_774_);
v_maxHeartbeats_775_ = lean_ctor_get(v_a_499_, 9);
lean_inc(v_maxHeartbeats_775_);
v_quotContext_776_ = lean_ctor_get(v_a_499_, 10);
lean_inc(v_quotContext_776_);
v_currMacroScope_777_ = lean_ctor_get(v_a_499_, 11);
lean_inc(v_currMacroScope_777_);
v_diag_778_ = lean_ctor_get_uint8(v_a_499_, sizeof(void*)*14);
v_cancelTk_x3f_779_ = lean_ctor_get(v_a_499_, 12);
lean_inc(v_cancelTk_x3f_779_);
v_suppressElabErrors_780_ = lean_ctor_get_uint8(v_a_499_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_781_ = lean_ctor_get(v_a_499_, 13);
lean_inc_ref(v_inheritedTraceOptions_781_);
lean_dec_ref(v_a_499_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_nat_dec_eq(v_maxRecDepth_770_, v___x_823_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = lean_nat_dec_eq(v_currRecDepth_769_, v_maxRecDepth_770_);
if (v___x_825_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v___x_826_; 
lean_dec_ref(v_inheritedTraceOptions_781_);
lean_dec(v_cancelTk_x3f_779_);
lean_dec(v_currMacroScope_777_);
lean_dec(v_quotContext_776_);
lean_dec(v_maxHeartbeats_775_);
lean_dec(v_initHeartbeats_774_);
lean_dec(v_openDecls_773_);
lean_dec(v_currNamespace_772_);
lean_dec(v_maxRecDepth_770_);
lean_dec(v_currRecDepth_769_);
lean_dec_ref(v_options_768_);
lean_dec_ref(v_fileMap_767_);
lean_dec_ref(v_fileName_766_);
lean_dec_ref(v_c_490_);
v___x_826_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_771_);
return v___x_826_;
}
}
else
{
goto v___jp_782_;
}
v___jp_502_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_513_; 
v___x_513_ = l_Int_Linear_Poly_updateOccs___redArg(v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec_ref(v___y_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v___x_513_);
v___x_514_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_515_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_514_, v___y_506_, v___y_508_);
return v___x_515_;
}
else
{
lean_dec_ref(v___y_506_);
return v___x_513_;
}
}
v___jp_516_:
{
if (lean_obj_tag(v___y_538_) == 1)
{
lean_object* v_val_539_; lean_object* v_p_540_; 
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_526_);
v_val_539_ = lean_ctor_get(v___y_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref(v___y_538_);
v_p_540_ = lean_ctor_get(v_val_539_, 1);
lean_inc_ref(v_p_540_);
if (lean_obj_tag(v_p_540_) == 1)
{
lean_object* v_d_541_; lean_object* v_k_542_; lean_object* v_p_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_596_; 
v_d_541_ = lean_ctor_get(v_val_539_, 0);
v_k_542_ = lean_ctor_get(v_p_540_, 0);
v_p_543_ = lean_ctor_get(v_p_540_, 2);
v_isSharedCheck_596_ = !lean_is_exclusive(v_p_540_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_p_540_, 1);
lean_dec(v_unused_597_);
v___x_545_ = v_p_540_;
v_isShared_546_ = v_isSharedCheck_596_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_p_543_);
lean_inc(v_k_542_);
lean_dec(v_p_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_596_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_snd_550_; lean_object* v_fst_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_595_; 
v___x_547_ = lean_int_mul(v___y_527_, v_d_541_);
v___x_548_ = lean_int_mul(v_k_542_, v___y_535_);
v___x_549_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_547_, v___x_548_);
lean_dec(v___x_548_);
lean_dec(v___x_547_);
v_snd_550_ = lean_ctor_get(v___x_549_, 1);
v_fst_551_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_595_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_595_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_551_);
lean_dec(v___x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_595_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_fst_555_; lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_594_; 
v_fst_555_ = lean_ctor_get(v_snd_550_, 0);
v_snd_556_ = lean_ctor_get(v_snd_550_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_snd_550_);
if (v_isSharedCheck_594_ == 0)
{
v___x_558_ = v_snd_550_;
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_inc(v_fst_555_);
lean_dec(v_snd_550_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_561_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_560_, v___y_530_, v___y_522_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec_ref(v___x_561_);
v___x_562_ = lean_int_mul(v_fst_555_, v_d_541_);
lean_dec(v_fst_555_);
lean_inc_ref(v___y_524_);
v___x_563_ = l_Int_Linear_Poly_mul(v___y_524_, v___x_562_);
lean_dec(v___x_562_);
v___x_564_ = lean_int_mul(v_snd_556_, v___y_535_);
lean_dec(v_snd_556_);
lean_inc_ref(v_p_543_);
v___x_565_ = l_Int_Linear_Poly_mul(v_p_543_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = lean_int_mul(v___y_535_, v_d_541_);
lean_dec(v___y_535_);
v___x_567_ = l_Int_Linear_Poly_combine(v___x_563_, v___x_565_);
lean_inc(v_fst_551_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 2, v___x_567_);
lean_ctor_set(v___x_545_, 1, v___y_518_);
lean_ctor_set(v___x_545_, 0, v_fst_551_);
v___x_569_ = v___x_545_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_fst_551_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___y_518_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v___x_567_);
v___x_569_ = v_reuseFailAlloc_593_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
lean_inc(v_val_539_);
lean_inc_ref(v___y_523_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 4);
lean_ctor_set(v___x_558_, 1, v_val_539_);
lean_ctor_set(v___x_558_, 0, v___y_523_);
v___x_571_ = v___x_558_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_val_539_);
v___x_571_ = v_reuseFailAlloc_592_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_566_);
lean_ctor_set(v___x_572_, 1, v___x_569_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
lean_inc_ref(v___y_517_);
v___x_573_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_572_, v___y_522_, v___y_534_, v___y_519_, v___y_520_, v___y_528_, v___y_533_, v___y_529_, v___y_537_, v___y_517_, v___y_536_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
lean_dec_ref(v___x_573_);
v___x_574_ = l_Int_Linear_Poly_mul(v___y_524_, v_k_542_);
lean_dec(v_k_542_);
v___x_575_ = lean_int_neg(v___y_527_);
lean_dec(v___y_527_);
v___x_576_ = l_Int_Linear_Poly_mul(v_p_543_, v___x_575_);
lean_dec(v___x_575_);
v___x_577_ = l_Int_Linear_Poly_combine(v___x_574_, v___x_576_);
lean_inc(v_val_539_);
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 5);
lean_ctor_set(v___x_553_, 1, v_val_539_);
lean_ctor_set(v___x_553_, 0, v___y_523_);
v___x_579_ = v___x_553_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_val_539_);
v___x_579_ = v_reuseFailAlloc_591_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_val_539_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_588_ = lean_ctor_get(v_val_539_, 2);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_val_539_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_val_539_, 0);
lean_dec(v_unused_590_);
v___x_581_ = v_val_539_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_val_539_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 0, v_fst_551_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_fst_551_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v___x_579_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_c_490_ = v___x_584_;
v_a_491_ = v___y_522_;
v_a_492_ = v___y_534_;
v_a_493_ = v___y_519_;
v_a_494_ = v___y_520_;
v_a_495_ = v___y_528_;
v_a_496_ = v___y_533_;
v_a_497_ = v___y_529_;
v_a_498_ = v___y_537_;
v_a_499_ = v___y_517_;
v_a_500_ = v___y_536_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_553_);
lean_dec(v_fst_551_);
lean_dec_ref(v_p_543_);
lean_dec(v_k_542_);
lean_dec(v_val_539_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_517_);
return v___x_573_;
}
}
}
}
else
{
lean_del_object(v___x_558_);
lean_dec(v_snd_556_);
lean_dec(v_fst_555_);
lean_del_object(v___x_553_);
lean_dec(v_fst_551_);
lean_del_object(v___x_545_);
lean_dec_ref(v_p_543_);
lean_dec(v_k_542_);
lean_dec(v_val_539_);
lean_dec(v___y_535_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec_ref(v_p_540_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_518_);
v___x_598_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_539_, v___y_522_, v___y_534_, v___y_519_, v___y_520_, v___y_528_, v___y_533_, v___y_529_, v___y_537_, v___y_517_, v___y_536_);
lean_dec_ref(v___y_517_);
return v___x_598_;
}
}
else
{
lean_object* v_options_599_; uint8_t v_hasTrace_600_; 
lean_dec(v___y_538_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_518_);
v_options_599_ = lean_ctor_get(v___y_517_, 2);
v_hasTrace_600_ = lean_ctor_get_uint8(v_options_599_, sizeof(void*)*1);
if (v_hasTrace_600_ == 0)
{
lean_dec_ref(v___y_523_);
v___y_506_ = v___y_531_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_522_;
v___y_509_ = v___y_529_;
v___y_510_ = v___y_537_;
v___y_511_ = v___y_517_;
v___y_512_ = v___y_536_;
goto v___jp_505_;
}
else
{
lean_object* v_inheritedTraceOptions_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_inheritedTraceOptions_601_ = lean_ctor_get(v___y_517_, 13);
v___x_602_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_525_);
lean_inc_ref(v___y_532_);
lean_inc_ref(v___y_521_);
v___x_603_ = l_Lean_Name_mkStr4(v___y_521_, v___y_532_, v___y_525_, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_603_);
v___x_605_ = l_Lean_Name_append(v___x_604_, v___x_603_);
v___x_606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_601_, v_options_599_, v___x_605_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v___x_603_);
lean_dec_ref(v___y_523_);
v___y_506_ = v___y_531_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_522_;
v___y_509_ = v___y_529_;
v___y_510_ = v___y_537_;
v___y_511_ = v___y_517_;
v___y_512_ = v___y_536_;
goto v___jp_505_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_523_, v___y_522_, v___y_517_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_603_, v_a_608_, v___y_529_, v___y_537_, v___y_517_, v___y_536_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_dec_ref(v___x_609_);
v___y_506_ = v___y_531_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_522_;
v___y_509_ = v___y_529_;
v___y_510_ = v___y_537_;
v___y_511_ = v___y_517_;
v___y_512_ = v___y_536_;
goto v___jp_505_;
}
else
{
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v___y_517_);
return v___x_609_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v___x_603_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v___y_517_);
v_a_610_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_607_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_607_);
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
}
}
}
v___jp_618_:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_630_, v___y_638_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_dvds_642_; lean_object* v_size_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v___x_640_);
v_dvds_642_ = lean_ctor_get(v_a_641_, 6);
lean_inc_ref(v_dvds_642_);
lean_dec(v_a_641_);
v_size_643_ = lean_ctor_get(v_dvds_642_, 2);
v___x_644_ = lean_box(0);
v___x_645_ = lean_nat_dec_lt(v___y_619_, v_size_643_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v_dvds_642_);
v___x_646_ = l_outOfBounds___redArg(v___x_644_);
v___y_517_ = v___y_638_;
v___y_518_ = v___y_619_;
v___y_519_ = v___y_632_;
v___y_520_ = v___y_633_;
v___y_521_ = v___y_620_;
v___y_522_ = v___y_630_;
v___y_523_ = v___y_621_;
v___y_524_ = v___y_625_;
v___y_525_ = v___y_627_;
v___y_526_ = v___y_628_;
v___y_527_ = v___y_629_;
v___y_528_ = v___y_634_;
v___y_529_ = v___y_636_;
v___y_530_ = v___y_622_;
v___y_531_ = v___y_624_;
v___y_532_ = v___y_623_;
v___y_533_ = v___y_635_;
v___y_534_ = v___y_631_;
v___y_535_ = v___y_626_;
v___y_536_ = v___y_639_;
v___y_537_ = v___y_637_;
v___y_538_ = v___x_646_;
goto v___jp_516_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentArray_get_x21___redArg(v___x_644_, v_dvds_642_, v___y_619_);
lean_dec_ref(v_dvds_642_);
v___y_517_ = v___y_638_;
v___y_518_ = v___y_619_;
v___y_519_ = v___y_632_;
v___y_520_ = v___y_633_;
v___y_521_ = v___y_620_;
v___y_522_ = v___y_630_;
v___y_523_ = v___y_621_;
v___y_524_ = v___y_625_;
v___y_525_ = v___y_627_;
v___y_526_ = v___y_628_;
v___y_527_ = v___y_629_;
v___y_528_ = v___y_634_;
v___y_529_ = v___y_636_;
v___y_530_ = v___y_622_;
v___y_531_ = v___y_624_;
v___y_532_ = v___y_623_;
v___y_533_ = v___y_635_;
v___y_534_ = v___y_631_;
v___y_535_ = v___y_626_;
v___y_536_ = v___y_639_;
v___y_537_ = v___y_637_;
v___y_538_ = v___x_647_;
goto v___jp_516_;
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v___y_638_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_619_);
v_a_648_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_640_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_640_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
v___jp_656_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___y_657_);
v___x_669_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_668_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec_ref(v___y_666_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_669_, 0);
lean_dec(v_unused_678_);
v___x_671_ = v___x_669_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_669_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
return v___x_669_;
}
}
v___jp_679_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_490_);
lean_inc_ref(v___y_691_);
v___x_694_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_693_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_d_696_; lean_object* v_p_697_; uint8_t v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v_d_696_ = lean_ctor_get(v_a_695_, 0);
v_p_697_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_d_696_);
v___x_698_ = l_Int_Linear_Poly_isUnsatDvd(v_d_696_, v_p_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_695_);
if (v___x_699_ == 0)
{
if (lean_obj_tag(v_p_697_) == 1)
{
lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v_p_702_; lean_object* v___x_703_; 
lean_inc_ref(v_p_697_);
lean_inc(v_d_696_);
v_k_700_ = lean_ctor_get(v_p_697_, 0);
lean_inc(v_k_700_);
v_v_701_ = lean_ctor_get(v_p_697_, 1);
lean_inc(v_v_701_);
v_p_702_ = lean_ctor_get(v_p_697_, 2);
lean_inc_ref(v_p_702_);
lean_inc(v_a_695_);
v___x_703_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_695_, v___y_683_, v___y_691_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___f_705_; lean_object* v___f_706_; uint8_t v___x_707_; uint8_t v___x_708_; uint8_t v___x_709_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
lean_inc_n(v_v_701_, 2);
lean_inc(v_a_695_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_705_, 0, v_a_695_);
lean_closure_set(v___f_705_, 1, v_v_701_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_706_, 0, v_v_701_);
v___x_707_ = 0;
v___x_708_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
v___x_709_ = l_Lean_instBEqLBool_beq(v___x_708_, v___x_707_);
if (v___x_709_ == 0)
{
v___y_619_ = v_v_701_;
v___y_620_ = v___y_680_;
v___y_621_ = v_a_695_;
v___y_622_ = v___f_706_;
v___y_623_ = v___y_681_;
v___y_624_ = v___f_705_;
v___y_625_ = v_p_702_;
v___y_626_ = v_d_696_;
v___y_627_ = v___y_682_;
v___y_628_ = v_p_697_;
v___y_629_ = v_k_700_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
goto v___jp_618_;
}
else
{
lean_object* v___x_710_; 
lean_inc(v_v_701_);
v___x_710_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_701_, v___y_683_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec_ref(v___x_710_);
v___y_619_ = v_v_701_;
v___y_620_ = v___y_680_;
v___y_621_ = v_a_695_;
v___y_622_ = v___f_706_;
v___y_623_ = v___y_681_;
v___y_624_ = v___f_705_;
v___y_625_ = v_p_702_;
v___y_626_ = v_d_696_;
v___y_627_ = v___y_682_;
v___y_628_ = v_p_697_;
v___y_629_ = v_k_700_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
goto v___jp_618_;
}
else
{
lean_dec_ref(v___f_706_);
lean_dec_ref(v___f_705_);
lean_dec_ref(v_p_702_);
lean_dec(v_v_701_);
lean_dec(v_k_700_);
lean_dec_ref(v_p_697_);
lean_dec(v_d_696_);
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
return v___x_710_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_p_702_);
lean_dec(v_v_701_);
lean_dec(v_k_700_);
lean_dec_ref(v_p_697_);
lean_dec(v_d_696_);
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
v_a_711_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_703_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_703_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_695_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v___y_691_);
return v___x_719_;
}
}
else
{
lean_object* v_options_720_; uint8_t v_hasTrace_721_; 
v_options_720_ = lean_ctor_get(v___y_691_, 2);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_720_, sizeof(void*)*1);
if (v_hasTrace_721_ == 0)
{
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
goto v___jp_502_;
}
else
{
lean_object* v_inheritedTraceOptions_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_inheritedTraceOptions_722_ = lean_ctor_get(v___y_691_, 13);
v___x_723_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc_ref(v___y_680_);
v___x_724_ = l_Lean_Name_mkStr4(v___y_680_, v___y_681_, v___y_682_, v___x_723_);
v___x_725_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_724_);
v___x_726_ = l_Lean_Name_append(v___x_725_, v___x_724_);
v___x_727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_722_, v_options_720_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v___x_724_);
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
goto v___jp_502_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_695_, v___y_683_, v___y_691_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
v___x_730_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_724_, v_a_729_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v___y_691_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_dec_ref(v___x_730_);
goto v___jp_502_;
}
else
{
return v___x_730_;
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v___x_724_);
lean_dec_ref(v___y_691_);
v_a_731_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_728_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_739_; uint8_t v_hasTrace_740_; 
v_options_739_ = lean_ctor_get(v___y_691_, 2);
v_hasTrace_740_ = lean_ctor_get_uint8(v_options_739_, sizeof(void*)*1);
if (v_hasTrace_740_ == 0)
{
v___y_657_ = v_a_695_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
goto v___jp_656_;
}
else
{
lean_object* v_inheritedTraceOptions_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_inheritedTraceOptions_741_ = lean_ctor_get(v___y_691_, 13);
v___x_742_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc_ref(v___y_680_);
v___x_743_ = l_Lean_Name_mkStr4(v___y_680_, v___y_681_, v___y_682_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_743_);
v___x_745_ = l_Lean_Name_append(v___x_744_, v___x_743_);
v___x_746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_741_, v_options_739_, v___x_745_);
lean_dec(v___x_745_);
if (v___x_746_ == 0)
{
lean_dec(v___x_743_);
v___y_657_ = v_a_695_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
goto v___jp_656_;
}
else
{
lean_object* v___x_747_; 
lean_inc(v_a_695_);
v___x_747_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_695_, v___y_683_, v___y_691_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v___x_749_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_743_, v_a_748_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref(v___x_749_);
v___y_657_ = v_a_695_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
goto v___jp_656_;
}
else
{
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
return v___x_749_;
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v___x_743_);
lean_dec(v_a_695_);
lean_dec_ref(v___y_691_);
v_a_750_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_747_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_747_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___y_691_);
v_a_758_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_694_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_694_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_currRecDepth_769_, v___x_783_);
lean_dec(v_currRecDepth_769_);
lean_inc_ref(v_inheritedTraceOptions_781_);
lean_inc_ref(v_options_768_);
v___x_785_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_785_, 0, v_fileName_766_);
lean_ctor_set(v___x_785_, 1, v_fileMap_767_);
lean_ctor_set(v___x_785_, 2, v_options_768_);
lean_ctor_set(v___x_785_, 3, v___x_784_);
lean_ctor_set(v___x_785_, 4, v_maxRecDepth_770_);
lean_ctor_set(v___x_785_, 5, v_ref_771_);
lean_ctor_set(v___x_785_, 6, v_currNamespace_772_);
lean_ctor_set(v___x_785_, 7, v_openDecls_773_);
lean_ctor_set(v___x_785_, 8, v_initHeartbeats_774_);
lean_ctor_set(v___x_785_, 9, v_maxHeartbeats_775_);
lean_ctor_set(v___x_785_, 10, v_quotContext_776_);
lean_ctor_set(v___x_785_, 11, v_currMacroScope_777_);
lean_ctor_set(v___x_785_, 12, v_cancelTk_x3f_779_);
lean_ctor_set(v___x_785_, 13, v_inheritedTraceOptions_781_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*14, v_diag_778_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*14 + 1, v_suppressElabErrors_780_);
v___x_786_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_491_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_814_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_814_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_814_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_814_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; 
v___x_791_ = lean_unbox(v_a_787_);
lean_dec(v_a_787_);
if (v___x_791_ == 0)
{
uint8_t v_hasTrace_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_789_);
v_hasTrace_792_ = lean_ctor_get_uint8(v_options_768_, sizeof(void*)*1);
v___x_793_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_792_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_781_);
lean_dec_ref(v_options_768_);
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v___x_795_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v___x_785_;
v___y_692_ = v_a_500_;
goto v___jp_679_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_797_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_781_, v_options_768_, v___x_797_);
lean_dec_ref(v_options_768_);
lean_dec_ref(v_inheritedTraceOptions_781_);
if (v___x_798_ == 0)
{
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v___x_795_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v___x_785_;
v___y_692_ = v_a_500_;
goto v___jp_679_;
}
else
{
lean_object* v___x_799_; 
lean_inc_ref(v_c_490_);
v___x_799_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_490_, v_a_491_, v___x_785_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_796_, v_a_800_, v_a_497_, v_a_498_, v___x_785_, v_a_500_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_dec_ref(v___x_801_);
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v___x_795_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v___x_785_;
v___y_692_ = v_a_500_;
goto v___jp_679_;
}
else
{
lean_dec_ref(v___x_785_);
lean_dec_ref(v_c_490_);
return v___x_801_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_c_490_);
v_a_802_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_799_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_inheritedTraceOptions_781_);
lean_dec_ref(v_options_768_);
lean_dec_ref(v_c_490_);
v___x_810_ = lean_box(0);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_810_);
v___x_812_ = v___x_789_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_inheritedTraceOptions_781_);
lean_dec_ref(v_options_768_);
lean_dec_ref(v_c_490_);
v_a_815_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_786_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_786_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec(v_a_828_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_d_852_; lean_object* v_p_853_; lean_object* v___x_854_; 
v_d_852_ = lean_ctor_get(v_c_840_, 0);
v_p_853_ = lean_ctor_get(v_c_840_, 1);
lean_inc_ref(v_p_853_);
v___x_854_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_853_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
if (lean_obj_tag(v_a_855_) == 1)
{
lean_object* v_val_856_; lean_object* v_snd_857_; lean_object* v_fst_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc(v_d_852_);
v_val_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref(v_a_855_);
v_snd_857_ = lean_ctor_get(v_val_856_, 1);
lean_inc(v_snd_857_);
v_fst_858_ = lean_ctor_get(v_val_856_, 0);
lean_inc(v_fst_858_);
lean_dec(v_val_856_);
v_fst_859_ = lean_ctor_get(v_snd_857_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v_snd_857_, 1);
lean_inc(v_snd_860_);
lean_dec(v_snd_857_);
v___x_861_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_861_, 0, v_c_840_);
lean_ctor_set(v___x_861_, 1, v_fst_858_);
lean_ctor_set(v___x_861_, 2, v_fst_859_);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v_d_852_);
lean_ctor_set(v___x_862_, 1, v_snd_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_inc_ref(v_a_849_);
v___x_863_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_862_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
lean_dec(v_a_855_);
lean_inc_ref(v_a_849_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_864_;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_c_840_);
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec(v_a_874_);
return v_res_885_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6));
v___x_900_ = l_Lean_mkConst(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_919_; 
lean_inc_ref(v_e_904_);
v___x_919_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_904_, v_a_912_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1053_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_1053_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1053_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l_Lean_Expr_cleanupAnnotations(v_a_920_);
v___x_930_ = l_Lean_Expr_isApp(v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v___x_929_);
lean_dec_ref(v_e_904_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_arg_931_ = lean_ctor_get(v___x_929_, 1);
lean_inc_ref(v_arg_931_);
v___x_932_ = l_Lean_Expr_appFnCleanup___redArg(v___x_929_);
v___x_933_ = l_Lean_Expr_isApp(v___x_932_);
if (v___x_933_ == 0)
{
lean_dec_ref(v___x_932_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_arg_934_ = lean_ctor_get(v___x_932_, 1);
lean_inc_ref(v_arg_934_);
v___x_935_ = l_Lean_Expr_appFnCleanup___redArg(v___x_932_);
v___x_936_ = l_Lean_Expr_isApp(v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v___x_935_);
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_arg_937_ = lean_ctor_get(v___x_935_, 1);
lean_inc_ref(v_arg_937_);
v___x_938_ = l_Lean_Expr_appFnCleanup___redArg(v___x_935_);
v___x_939_ = l_Lean_Expr_isApp(v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___x_938_);
lean_dec_ref(v_arg_937_);
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
goto v___jp_924_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_938_);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_942_ = l_Lean_Expr_isConstOf(v___x_940_, v___x_941_);
lean_dec_ref(v___x_940_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_arg_937_);
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
goto v___jp_924_;
}
else
{
lean_object* v___x_943_; 
lean_del_object(v___x_922_);
v___x_943_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_937_, v_a_912_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1044_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_1044_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1044_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_948_; 
v___x_948_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v___x_949_ = lean_box(0);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v___x_953_; 
lean_del_object(v___x_946_);
lean_inc_ref(v_arg_934_);
v___x_953_ = l_Lean_Meta_getIntValue_x3f(v_arg_934_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref(v___x_953_);
if (lean_obj_tag(v_a_954_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1020_; 
v_val_955_ = lean_ctor_get(v_a_954_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_957_ = v_a_954_;
v_isShared_958_ = v_isSharedCheck_1020_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v_a_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1020_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; 
lean_inc_ref(v_e_904_);
v___x_959_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_904_, v_a_905_, v_a_909_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = lean_unbox(v_a_960_);
lean_dec(v_a_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_del_object(v___x_957_);
lean_dec(v_val_955_);
lean_inc_ref(v_e_904_);
v___x_962_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_904_, v_a_905_, v_a_909_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_988_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_988_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_988_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_988_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
uint8_t v___x_967_; 
v___x_967_ = lean_unbox(v_a_963_);
lean_dec(v_a_963_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v___x_968_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_972_; 
lean_del_object(v___x_965_);
lean_inc_ref(v_e_904_);
v___x_972_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
v___x_975_ = l_Lean_eagerReflBoolTrue;
v___x_976_ = l_Lean_Meta_mkOfEqFalseCore(v_e_904_, v_a_973_);
v___x_977_ = l_Lean_mkApp4(v___x_974_, v_arg_934_, v_arg_931_, v___x_975_, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = l_Lean_Meta_Grind_pushNewFact(v___x_977_, v___x_978_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v_a_980_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_972_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_972_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v_a_989_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_962_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_962_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v___x_997_; 
lean_dec_ref(v_arg_934_);
v___x_997_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_931_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
lean_ctor_set(v___x_957_, 0, v_e_904_);
v___x_1000_ = v___x_957_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_e_904_);
v___x_1000_ = v_reuseFailAlloc_1003_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v_val_955_);
lean_ctor_set(v___x_1001_, 1, v_a_998_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
v___x_1002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1001_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_957_);
lean_dec(v_val_955_);
lean_dec_ref(v_e_904_);
v_a_1004_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_997_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_957_);
lean_dec(v_val_955_);
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v_a_1012_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_959_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_959_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
else
{
lean_object* v___x_1021_; 
lean_dec(v_a_954_);
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
v___x_1021_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_909_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; uint8_t v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = lean_unbox(v_a_1022_);
lean_dec(v_a_1022_);
if (v___x_1023_ == 0)
{
lean_dec_ref(v_e_904_);
goto v___jp_916_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1025_ = l_Lean_indentExpr(v_e_904_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_Meta_Sym_reportIssue(v___x_1026_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_dec_ref(v___x_1027_);
goto v___jp_916_;
}
else
{
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_e_904_);
v_a_1028_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1021_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1021_);
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
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v_a_1036_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_953_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_953_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_arg_934_);
lean_dec_ref(v_arg_931_);
lean_dec_ref(v_e_904_);
v_a_1045_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_943_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_943_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
}
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_e_904_);
v_a_1054_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_919_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_919_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec(v_a_1063_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_nat_to_int(v_a_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1084_ = l_Lean_mkConst(v___x_1083_, v___x_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1093_ = l_Lean_mkConst(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
lean_inc_ref(v_e_1094_);
v___x_1112_ = l_Lean_Expr_cleanupAnnotations(v_e_1094_);
v___x_1113_ = l_Lean_Expr_isApp(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_e_1094_);
goto v___jp_1106_;
}
else
{
lean_object* v_arg_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_arg_1114_ = lean_ctor_get(v___x_1112_, 1);
lean_inc_ref(v_arg_1114_);
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1112_);
v___x_1116_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
goto v___jp_1106_;
}
else
{
lean_object* v_arg_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_arg_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc_ref(v_arg_1117_);
v___x_1118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
v___x_1119_ = l_Lean_Expr_isApp(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
goto v___jp_1106_;
}
else
{
lean_object* v_arg_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_arg_1120_ = lean_ctor_get(v___x_1118_, 1);
lean_inc_ref(v_arg_1120_);
v___x_1121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1118_);
v___x_1122_ = l_Lean_Expr_isApp(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
goto v___jp_1106_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1121_);
v___x_1124_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1125_ = l_Lean_Expr_isConstOf(v___x_1123_, v___x_1124_);
lean_dec_ref(v___x_1123_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
goto v___jp_1106_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1120_, v_a_1102_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1258_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1258_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1258_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v___x_1132_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v___x_1136_; 
lean_del_object(v___x_1129_);
v___x_1136_ = l_Lean_Meta_getNatValue_x3f(v_arg_1117_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
if (lean_obj_tag(v_a_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v_a_1137_);
lean_inc_ref(v_e_1094_);
v___x_1139_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1094_, v_a_1095_, v_a_1099_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; uint8_t v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
v___x_1141_ = lean_unbox(v_a_1140_);
lean_dec(v_a_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v_val_1138_);
lean_inc_ref(v_e_1094_);
v___x_1142_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1094_, v_a_1095_, v_a_1099_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v___x_1148_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___x_1152_; 
lean_del_object(v___x_1145_);
lean_inc_ref(v_e_1094_);
v___x_1152_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1155_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1094_, v_a_1153_);
v___x_1156_ = l_Lean_mkApp3(v___x_1154_, v_arg_1117_, v_arg_1114_, v___x_1155_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Lean_Meta_Grind_pushNewFact(v___x_1156_, v___x_1157_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1158_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1159_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1152_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1152_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1168_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1142_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1142_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v___x_1176_; 
lean_inc_ref(v_arg_1117_);
v___x_1176_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1117_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
v_fst_1178_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v_a_1177_, 1);
lean_inc(v_snd_1179_);
lean_dec(v_a_1177_);
lean_inc_ref(v_arg_1114_);
v___x_1180_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1114_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
v_fst_1182_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_fst_1182_);
v_snd_1183_ = lean_ctor_get(v_a_1181_, 1);
lean_inc(v_snd_1183_);
lean_dec(v_a_1181_);
v___x_1184_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
lean_inc(v_fst_1182_);
v___x_1186_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1182_, v_a_1185_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = l_Int_Linear_Expr_norm(v_a_1187_);
v___x_1189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1190_ = l_Lean_mkApp6(v___x_1189_, v_arg_1117_, v_arg_1114_, v_fst_1178_, v_fst_1182_, v_snd_1179_, v_snd_1183_);
lean_inc(v_val_1138_);
v___x_1191_ = lean_nat_to_int(v_val_1138_);
v___x_1192_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1192_, 0, v_e_1094_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v_val_1138_);
lean_ctor_set(v___x_1192_, 3, v_a_1187_);
v___x_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1188_);
lean_ctor_set(v___x_1193_, 2, v___x_1192_);
v___x_1194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1193_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
lean_dec(v_snd_1179_);
lean_dec(v_fst_1178_);
lean_dec(v_val_1138_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1186_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
lean_dec(v_snd_1179_);
lean_dec(v_fst_1178_);
lean_dec(v_val_1138_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1203_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1184_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1184_);
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
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_snd_1179_);
lean_dec(v_fst_1178_);
lean_dec(v_val_1138_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1211_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1180_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1180_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_val_1138_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1219_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1176_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1176_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_val_1138_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1227_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1139_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1139_);
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
lean_object* v___x_1235_; 
lean_dec(v_a_1137_);
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
v___x_1235_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1099_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v_e_1094_);
goto v___jp_1109_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1239_ = l_Lean_indentExpr(v_e_1094_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = l_Lean_Meta_Sym_reportIssue(v___x_1240_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_dec_ref(v___x_1241_);
goto v___jp_1109_;
}
else
{
return v___x_1241_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_e_1094_);
v_a_1242_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1235_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1235_);
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
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1250_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1136_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1136_);
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
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_arg_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_e_1094_);
v_a_1259_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1126_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1126_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec(v_a_1268_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1285_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1339_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1339_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1339_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
uint8_t v_lia_1299_; 
v_lia_1299_ = lean_ctor_get_uint8(v_a_1295_, sizeof(void*)*12 + 23);
lean_dec(v_a_1295_);
if (v_lia_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec_ref(v_e_1282_);
v___x_1300_ = lean_box(0);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
else
{
lean_object* v___x_1304_; 
lean_del_object(v___x_1297_);
lean_inc_ref(v_e_1282_);
v___x_1304_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1282_, v_a_1290_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1330_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1330_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1330_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = l_Lean_Expr_cleanupAnnotations(v_a_1305_);
v___x_1315_ = l_Lean_Expr_isApp(v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1282_);
goto v___jp_1309_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1314_);
v___x_1317_ = l_Lean_Expr_isApp(v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_e_1282_);
goto v___jp_1309_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1316_);
v___x_1319_ = l_Lean_Expr_isApp(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_e_1282_);
goto v___jp_1309_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1318_);
v___x_1321_ = l_Lean_Expr_isApp(v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_e_1282_);
goto v___jp_1309_;
}
else
{
lean_object* v_arg_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_arg_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc_ref(v_arg_1322_);
v___x_1323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1320_);
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1325_ = l_Lean_Expr_isConstOf(v___x_1323_, v___x_1324_);
lean_dec_ref(v___x_1323_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v_arg_1322_);
lean_dec_ref(v_e_1282_);
goto v___jp_1309_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_del_object(v___x_1307_);
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1327_ = l_Lean_Expr_isConstOf(v_arg_1322_, v___x_1326_);
lean_dec_ref(v_arg_1322_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1329_;
}
}
}
}
}
}
v___jp_1309_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_e_1282_);
v_a_1331_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1304_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1304_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v_e_1282_);
v_a_1340_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1294_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1294_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec(v_a_1349_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1363_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1364_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1362_, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return v_res_1366_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
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
