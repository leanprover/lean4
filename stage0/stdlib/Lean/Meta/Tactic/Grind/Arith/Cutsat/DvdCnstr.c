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
lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_122_; 
v_ref_75_ = lean_ctor_get(v___y_72_, 5);
v___x_76_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_122_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_122_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_122_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v_traceState_82_; lean_object* v_env_83_; lean_object* v_nextMacroScope_84_; lean_object* v_ngen_85_; lean_object* v_auxDeclNGen_86_; lean_object* v_cache_87_; lean_object* v_messages_88_; lean_object* v_infoState_89_; lean_object* v_snapshotTasks_90_; lean_object* v_newDecls_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_121_; 
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
v_newDecls_91_ = lean_ctor_get(v___x_81_, 9);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_121_ == 0)
{
v___x_93_ = v___x_81_;
v_isShared_94_ = v_isSharedCheck_121_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_newDecls_91_);
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
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_121_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint64_t v_tid_95_; lean_object* v_traces_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_120_; 
v_tid_95_ = lean_ctor_get_uint64(v_traceState_82_, sizeof(void*)*1);
v_traces_96_ = lean_ctor_get(v_traceState_82_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_traceState_82_);
if (v_isSharedCheck_120_ == 0)
{
v___x_98_ = v_traceState_82_;
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_traces_96_);
lean_dec(v_traceState_82_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; double v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_100_ = lean_box(0);
v___x_101_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_102_ = 0;
v___x_103_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_104_, 0, v_cls_68_);
lean_ctor_set(v___x_104_, 1, v___x_100_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_ctor_set_float(v___x_104_, sizeof(void*)*3, v___x_101_);
lean_ctor_set_float(v___x_104_, sizeof(void*)*3 + 8, v___x_101_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*3 + 16, v___x_102_);
v___x_105_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v_a_77_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
lean_inc(v_ref_75_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_ref_75_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_PersistentArray_push___redArg(v_traces_96_, v___x_107_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_108_);
v___x_110_ = v___x_98_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_108_);
lean_ctor_set_uint64(v_reuseFailAlloc_119_, sizeof(void*)*1, v_tid_95_);
v___x_110_ = v_reuseFailAlloc_119_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_110_);
v___x_112_ = v___x_93_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_env_83_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_nextMacroScope_84_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_ngen_85_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_auxDeclNGen_86_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_118_, 5, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_118_, 6, v_messages_88_);
lean_ctor_set(v_reuseFailAlloc_118_, 7, v_infoState_89_);
lean_ctor_set(v_reuseFailAlloc_118_, 8, v_snapshotTasks_90_);
lean_ctor_set(v_reuseFailAlloc_118_, 9, v_newDecls_91_);
v___x_112_ = v_reuseFailAlloc_118_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = lean_st_ref_set(v___y_73_, v___x_112_);
v___x_114_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_114_);
v___x_116_ = v___x_79_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_123_, v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_cls_143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_145_ = l_Lean_Name_append(v___x_144_, v_cls_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_149_, lean_object* v_x_150_, lean_object* v_c_u2081_151_, lean_object* v_b_152_, lean_object* v_c_u2082_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_options_165_; lean_object* v_p_166_; lean_object* v_d_167_; lean_object* v_p_168_; lean_object* v_inheritedTraceOptions_169_; uint8_t v_hasTrace_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_d_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_p_177_; 
v_options_165_ = lean_ctor_get(v_a_162_, 2);
v_p_166_ = lean_ctor_get(v_c_u2081_151_, 0);
v_d_167_ = lean_ctor_get(v_c_u2082_153_, 0);
v_p_168_ = lean_ctor_get(v_c_u2082_153_, 1);
v_inheritedTraceOptions_169_ = lean_ctor_get(v_a_162_, 13);
v_hasTrace_170_ = lean_ctor_get_uint8(v_options_165_, sizeof(void*)*1);
v___x_171_ = lean_int_mul(v_a_149_, v_d_167_);
v___x_172_ = lean_nat_abs(v___x_171_);
lean_dec(v___x_171_);
v_d_173_ = lean_nat_to_int(v___x_172_);
lean_inc_ref(v_p_168_);
v___x_174_ = l_Int_Linear_Poly_mul(v_p_168_, v_a_149_);
v___x_175_ = lean_int_neg(v_b_152_);
lean_inc_ref(v_p_166_);
v___x_176_ = l_Int_Linear_Poly_mul(v_p_166_, v___x_175_);
lean_dec(v___x_175_);
v_p_177_ = l_Int_Linear_Poly_combine(v___x_174_, v___x_176_);
if (v_hasTrace_170_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v_cls_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_cls_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_169_, v_options_165_, v___x_183_);
if (v___x_184_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_150_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v___x_185_);
lean_inc_ref(v_c_u2081_151_);
v___x_187_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_151_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref(v___x_187_);
lean_inc_ref(v_c_u2082_153_);
v___x_189_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_153_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_189_);
v___x_191_ = l_Lean_MessageData_ofExpr(v_a_186_);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_188_);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_192_);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_190_);
v___x_197_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_182_, v___x_196_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_dec_ref(v___x_197_);
goto v___jp_178_;
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_188_);
lean_dec(v_a_186_);
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_206_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_189_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_189_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_186_);
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_214_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_187_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_187_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_222_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_185_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_185_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_179_, 0, v_x_150_);
lean_ctor_set(v___x_179_, 1, v_c_u2081_151_);
lean_ctor_set(v___x_179_, 2, v_c_u2082_153_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_d_173_);
lean_ctor_set(v___x_180_, 1, v_p_177_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_230_, lean_object* v_x_231_, lean_object* v_c_u2081_232_, lean_object* v_b_233_, lean_object* v_c_u2082_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_230_, v_x_231_, v_c_u2081_232_, v_b_233_, v_c_u2082_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_b_233_);
lean_dec(v_a_230_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_247_, v_msg_248_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_261_, lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_261_, v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec(v___y_263_);
return v_res_274_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Lean_maxRecDepthErrorMessage;
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_283_ = l_Lean_MessageData_ofFormat(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_285_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_286_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_287_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_ref_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_295_, lean_object* v_ref_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_296_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_309_, lean_object* v_ref_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_309_, v_ref_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_311_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_p_335_; lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_currRecDepth_339_; lean_object* v_maxRecDepth_340_; lean_object* v_ref_341_; lean_object* v_currNamespace_342_; lean_object* v_openDecls_343_; lean_object* v_initHeartbeats_344_; lean_object* v_maxHeartbeats_345_; lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; uint8_t v_diag_348_; lean_object* v_cancelTk_x3f_349_; uint8_t v_suppressElabErrors_350_; lean_object* v_inheritedTraceOptions_351_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_p_335_ = lean_ctor_get(v_c_323_, 1);
v_fileName_336_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_fileName_336_);
v_fileMap_337_ = lean_ctor_get(v_a_332_, 1);
lean_inc_ref(v_fileMap_337_);
v_options_338_ = lean_ctor_get(v_a_332_, 2);
lean_inc_ref(v_options_338_);
v_currRecDepth_339_ = lean_ctor_get(v_a_332_, 3);
lean_inc(v_currRecDepth_339_);
v_maxRecDepth_340_ = lean_ctor_get(v_a_332_, 4);
lean_inc(v_maxRecDepth_340_);
v_ref_341_ = lean_ctor_get(v_a_332_, 5);
lean_inc(v_ref_341_);
v_currNamespace_342_ = lean_ctor_get(v_a_332_, 6);
lean_inc(v_currNamespace_342_);
v_openDecls_343_ = lean_ctor_get(v_a_332_, 7);
lean_inc(v_openDecls_343_);
v_initHeartbeats_344_ = lean_ctor_get(v_a_332_, 8);
lean_inc(v_initHeartbeats_344_);
v_maxHeartbeats_345_ = lean_ctor_get(v_a_332_, 9);
lean_inc(v_maxHeartbeats_345_);
v_quotContext_346_ = lean_ctor_get(v_a_332_, 10);
lean_inc(v_quotContext_346_);
v_currMacroScope_347_ = lean_ctor_get(v_a_332_, 11);
lean_inc(v_currMacroScope_347_);
v_diag_348_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14);
v_cancelTk_x3f_349_ = lean_ctor_get(v_a_332_, 12);
lean_inc(v_cancelTk_x3f_349_);
v_suppressElabErrors_350_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_351_ = lean_ctor_get(v_a_332_, 13);
lean_inc_ref(v_inheritedTraceOptions_351_);
lean_dec_ref(v_a_332_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_nat_dec_eq(v_maxRecDepth_340_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_eq(v_currRecDepth_339_, v_maxRecDepth_340_);
if (v___x_385_ == 0)
{
goto v___jp_352_;
}
else
{
lean_object* v___x_386_; 
lean_dec_ref(v_inheritedTraceOptions_351_);
lean_dec(v_cancelTk_x3f_349_);
lean_dec(v_currMacroScope_347_);
lean_dec(v_quotContext_346_);
lean_dec(v_maxHeartbeats_345_);
lean_dec(v_initHeartbeats_344_);
lean_dec(v_openDecls_343_);
lean_dec(v_currNamespace_342_);
lean_dec(v_maxRecDepth_340_);
lean_dec(v_currRecDepth_339_);
lean_dec_ref(v_options_338_);
lean_dec_ref(v_fileMap_337_);
lean_dec_ref(v_fileName_336_);
lean_dec_ref(v_c_323_);
v___x_386_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_341_);
return v___x_386_;
}
}
else
{
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_currRecDepth_339_, v___x_353_);
lean_dec(v_currRecDepth_339_);
v___x_355_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_355_, 0, v_fileName_336_);
lean_ctor_set(v___x_355_, 1, v_fileMap_337_);
lean_ctor_set(v___x_355_, 2, v_options_338_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
lean_ctor_set(v___x_355_, 4, v_maxRecDepth_340_);
lean_ctor_set(v___x_355_, 5, v_ref_341_);
lean_ctor_set(v___x_355_, 6, v_currNamespace_342_);
lean_ctor_set(v___x_355_, 7, v_openDecls_343_);
lean_ctor_set(v___x_355_, 8, v_initHeartbeats_344_);
lean_ctor_set(v___x_355_, 9, v_maxHeartbeats_345_);
lean_ctor_set(v___x_355_, 10, v_quotContext_346_);
lean_ctor_set(v___x_355_, 11, v_currMacroScope_347_);
lean_ctor_set(v___x_355_, 12, v_cancelTk_x3f_349_);
lean_ctor_set(v___x_355_, 13, v_inheritedTraceOptions_351_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*14, v_diag_348_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*14 + 1, v_suppressElabErrors_350_);
lean_inc_ref(v_p_335_);
v___x_356_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_335_, v_a_324_, v___x_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_374_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_374_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_374_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_374_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_361_; lean_object* v_snd_362_; lean_object* v_snd_363_; lean_object* v_fst_364_; lean_object* v_fst_365_; lean_object* v_p_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_del_object(v___x_359_);
v_val_361_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_val_361_);
lean_dec_ref(v_a_357_);
v_snd_362_ = lean_ctor_get(v_val_361_, 1);
lean_inc(v_snd_362_);
v_snd_363_ = lean_ctor_get(v_snd_362_, 1);
lean_inc(v_snd_363_);
v_fst_364_ = lean_ctor_get(v_val_361_, 0);
lean_inc(v_fst_364_);
lean_dec(v_val_361_);
v_fst_365_ = lean_ctor_get(v_snd_362_, 0);
lean_inc(v_fst_365_);
lean_dec(v_snd_362_);
v_p_366_ = lean_ctor_get(v_snd_363_, 0);
v___x_367_ = l_Int_Linear_Poly_coeff(v_p_366_, v_fst_365_);
v___x_368_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_367_, v_fst_365_, v_snd_363_, v_fst_364_, v_c_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_355_, v_a_333_);
lean_dec(v_fst_364_);
lean_dec(v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v_c_323_ = v_a_369_;
v_a_332_ = v___x_355_;
goto _start;
}
else
{
lean_dec_ref(v___x_355_);
return v___x_368_;
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_a_357_);
lean_dec_ref(v___x_355_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v_c_323_);
v___x_372_ = v___x_359_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_c_323_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v___x_355_);
lean_dec_ref(v_c_323_);
v_a_375_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_356_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_356_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec(v_a_388_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_400_, lean_object* v_v_401_, lean_object* v_s_402_){
_start:
{
lean_object* v_vars_403_; lean_object* v_varMap_404_; lean_object* v_vars_x27_405_; lean_object* v_varMap_x27_406_; lean_object* v_natToIntMap_407_; lean_object* v_natDef_408_; lean_object* v_dvds_409_; lean_object* v_lowers_410_; lean_object* v_uppers_411_; lean_object* v_diseqs_412_; lean_object* v_elimEqs_413_; lean_object* v_elimStack_414_; lean_object* v_occurs_415_; lean_object* v_assignment_416_; lean_object* v_nextCnstrId_417_; uint8_t v_caseSplits_418_; lean_object* v_conflict_x3f_419_; lean_object* v_diseqSplits_420_; lean_object* v_divMod_421_; lean_object* v_toIntIds_422_; lean_object* v_toIntInfos_423_; lean_object* v_toIntTermMap_424_; lean_object* v_toIntVarMap_425_; uint8_t v_usedCommRing_426_; lean_object* v_nonlinearOccs_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
v_vars_403_ = lean_ctor_get(v_s_402_, 0);
v_varMap_404_ = lean_ctor_get(v_s_402_, 1);
v_vars_x27_405_ = lean_ctor_get(v_s_402_, 2);
v_varMap_x27_406_ = lean_ctor_get(v_s_402_, 3);
v_natToIntMap_407_ = lean_ctor_get(v_s_402_, 4);
v_natDef_408_ = lean_ctor_get(v_s_402_, 5);
v_dvds_409_ = lean_ctor_get(v_s_402_, 6);
v_lowers_410_ = lean_ctor_get(v_s_402_, 7);
v_uppers_411_ = lean_ctor_get(v_s_402_, 8);
v_diseqs_412_ = lean_ctor_get(v_s_402_, 9);
v_elimEqs_413_ = lean_ctor_get(v_s_402_, 10);
v_elimStack_414_ = lean_ctor_get(v_s_402_, 11);
v_occurs_415_ = lean_ctor_get(v_s_402_, 12);
v_assignment_416_ = lean_ctor_get(v_s_402_, 13);
v_nextCnstrId_417_ = lean_ctor_get(v_s_402_, 14);
v_caseSplits_418_ = lean_ctor_get_uint8(v_s_402_, sizeof(void*)*23);
v_conflict_x3f_419_ = lean_ctor_get(v_s_402_, 15);
v_diseqSplits_420_ = lean_ctor_get(v_s_402_, 16);
v_divMod_421_ = lean_ctor_get(v_s_402_, 17);
v_toIntIds_422_ = lean_ctor_get(v_s_402_, 18);
v_toIntInfos_423_ = lean_ctor_get(v_s_402_, 19);
v_toIntTermMap_424_ = lean_ctor_get(v_s_402_, 20);
v_toIntVarMap_425_ = lean_ctor_get(v_s_402_, 21);
v_usedCommRing_426_ = lean_ctor_get_uint8(v_s_402_, sizeof(void*)*23 + 1);
v_nonlinearOccs_427_ = lean_ctor_get(v_s_402_, 22);
v_isSharedCheck_436_ = !lean_is_exclusive(v_s_402_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v_s_402_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_nonlinearOccs_427_);
lean_inc(v_toIntVarMap_425_);
lean_inc(v_toIntTermMap_424_);
lean_inc(v_toIntInfos_423_);
lean_inc(v_toIntIds_422_);
lean_inc(v_divMod_421_);
lean_inc(v_diseqSplits_420_);
lean_inc(v_conflict_x3f_419_);
lean_inc(v_nextCnstrId_417_);
lean_inc(v_assignment_416_);
lean_inc(v_occurs_415_);
lean_inc(v_elimStack_414_);
lean_inc(v_elimEqs_413_);
lean_inc(v_diseqs_412_);
lean_inc(v_uppers_411_);
lean_inc(v_lowers_410_);
lean_inc(v_dvds_409_);
lean_inc(v_natDef_408_);
lean_inc(v_natToIntMap_407_);
lean_inc(v_varMap_x27_406_);
lean_inc(v_vars_x27_405_);
lean_inc(v_varMap_404_);
lean_inc(v_vars_403_);
lean_dec(v_s_402_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_400_);
v___x_432_ = l_Lean_PersistentArray_set___redArg(v_dvds_409_, v_v_401_, v___x_431_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 6, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_vars_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_varMap_404_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_vars_x27_405_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_varMap_x27_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_natToIntMap_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_natDef_408_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_lowers_410_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_uppers_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_diseqs_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_elimEqs_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 11, v_elimStack_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 12, v_occurs_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 13, v_assignment_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 14, v_nextCnstrId_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 15, v_conflict_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 16, v_diseqSplits_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 17, v_divMod_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 18, v_toIntIds_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 19, v_toIntInfos_423_);
lean_ctor_set(v_reuseFailAlloc_435_, 20, v_toIntTermMap_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 21, v_toIntVarMap_425_);
lean_ctor_set(v_reuseFailAlloc_435_, 22, v_nonlinearOccs_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*23, v_caseSplits_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*23 + 1, v_usedCommRing_426_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_437_, lean_object* v_v_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_437_, v_v_438_, v_s_439_);
lean_dec(v_v_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_441_, lean_object* v_s_442_){
_start:
{
lean_object* v_vars_443_; lean_object* v_varMap_444_; lean_object* v_vars_x27_445_; lean_object* v_varMap_x27_446_; lean_object* v_natToIntMap_447_; lean_object* v_natDef_448_; lean_object* v_dvds_449_; lean_object* v_lowers_450_; lean_object* v_uppers_451_; lean_object* v_diseqs_452_; lean_object* v_elimEqs_453_; lean_object* v_elimStack_454_; lean_object* v_occurs_455_; lean_object* v_assignment_456_; lean_object* v_nextCnstrId_457_; uint8_t v_caseSplits_458_; lean_object* v_conflict_x3f_459_; lean_object* v_diseqSplits_460_; lean_object* v_divMod_461_; lean_object* v_toIntIds_462_; lean_object* v_toIntInfos_463_; lean_object* v_toIntTermMap_464_; lean_object* v_toIntVarMap_465_; uint8_t v_usedCommRing_466_; lean_object* v_nonlinearOccs_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_vars_443_ = lean_ctor_get(v_s_442_, 0);
v_varMap_444_ = lean_ctor_get(v_s_442_, 1);
v_vars_x27_445_ = lean_ctor_get(v_s_442_, 2);
v_varMap_x27_446_ = lean_ctor_get(v_s_442_, 3);
v_natToIntMap_447_ = lean_ctor_get(v_s_442_, 4);
v_natDef_448_ = lean_ctor_get(v_s_442_, 5);
v_dvds_449_ = lean_ctor_get(v_s_442_, 6);
v_lowers_450_ = lean_ctor_get(v_s_442_, 7);
v_uppers_451_ = lean_ctor_get(v_s_442_, 8);
v_diseqs_452_ = lean_ctor_get(v_s_442_, 9);
v_elimEqs_453_ = lean_ctor_get(v_s_442_, 10);
v_elimStack_454_ = lean_ctor_get(v_s_442_, 11);
v_occurs_455_ = lean_ctor_get(v_s_442_, 12);
v_assignment_456_ = lean_ctor_get(v_s_442_, 13);
v_nextCnstrId_457_ = lean_ctor_get(v_s_442_, 14);
v_caseSplits_458_ = lean_ctor_get_uint8(v_s_442_, sizeof(void*)*23);
v_conflict_x3f_459_ = lean_ctor_get(v_s_442_, 15);
v_diseqSplits_460_ = lean_ctor_get(v_s_442_, 16);
v_divMod_461_ = lean_ctor_get(v_s_442_, 17);
v_toIntIds_462_ = lean_ctor_get(v_s_442_, 18);
v_toIntInfos_463_ = lean_ctor_get(v_s_442_, 19);
v_toIntTermMap_464_ = lean_ctor_get(v_s_442_, 20);
v_toIntVarMap_465_ = lean_ctor_get(v_s_442_, 21);
v_usedCommRing_466_ = lean_ctor_get_uint8(v_s_442_, sizeof(void*)*23 + 1);
v_nonlinearOccs_467_ = lean_ctor_get(v_s_442_, 22);
v_isSharedCheck_476_ = !lean_is_exclusive(v_s_442_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v_s_442_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_nonlinearOccs_467_);
lean_inc(v_toIntVarMap_465_);
lean_inc(v_toIntTermMap_464_);
lean_inc(v_toIntInfos_463_);
lean_inc(v_toIntIds_462_);
lean_inc(v_divMod_461_);
lean_inc(v_diseqSplits_460_);
lean_inc(v_conflict_x3f_459_);
lean_inc(v_nextCnstrId_457_);
lean_inc(v_assignment_456_);
lean_inc(v_occurs_455_);
lean_inc(v_elimStack_454_);
lean_inc(v_elimEqs_453_);
lean_inc(v_diseqs_452_);
lean_inc(v_uppers_451_);
lean_inc(v_lowers_450_);
lean_inc(v_dvds_449_);
lean_inc(v_natDef_448_);
lean_inc(v_natToIntMap_447_);
lean_inc(v_varMap_x27_446_);
lean_inc(v_vars_x27_445_);
lean_inc(v_varMap_444_);
lean_inc(v_vars_443_);
lean_dec(v_s_442_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_PersistentArray_set___redArg(v_dvds_449_, v_v_441_, v___x_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 6, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_vars_443_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_varMap_444_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_vars_x27_445_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_varMap_x27_446_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_natToIntMap_447_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_natDef_448_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_lowers_450_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_uppers_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_diseqs_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_elimEqs_453_);
lean_ctor_set(v_reuseFailAlloc_475_, 11, v_elimStack_454_);
lean_ctor_set(v_reuseFailAlloc_475_, 12, v_occurs_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 13, v_assignment_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 14, v_nextCnstrId_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 15, v_conflict_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 16, v_diseqSplits_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 17, v_divMod_461_);
lean_ctor_set(v_reuseFailAlloc_475_, 18, v_toIntIds_462_);
lean_ctor_set(v_reuseFailAlloc_475_, 19, v_toIntInfos_463_);
lean_ctor_set(v_reuseFailAlloc_475_, 20, v_toIntTermMap_464_);
lean_ctor_set(v_reuseFailAlloc_475_, 21, v_toIntVarMap_465_);
lean_ctor_set(v_reuseFailAlloc_475_, 22, v_nonlinearOccs_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*23, v_caseSplits_458_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*23 + 1, v_usedCommRing_466_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_477_, lean_object* v_s_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_477_, v_s_478_);
lean_dec(v_v_477_);
return v_res_479_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_489_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_490_ = l_Lean_Name_append(v___x_489_, v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v_fileName_767_; lean_object* v_fileMap_768_; lean_object* v_options_769_; lean_object* v_currRecDepth_770_; lean_object* v_maxRecDepth_771_; lean_object* v_ref_772_; lean_object* v_currNamespace_773_; lean_object* v_openDecls_774_; lean_object* v_initHeartbeats_775_; lean_object* v_maxHeartbeats_776_; lean_object* v_quotContext_777_; lean_object* v_currMacroScope_778_; uint8_t v_diag_779_; lean_object* v_cancelTk_x3f_780_; uint8_t v_suppressElabErrors_781_; lean_object* v_inheritedTraceOptions_782_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_fileName_767_ = lean_ctor_get(v_a_500_, 0);
lean_inc_ref(v_fileName_767_);
v_fileMap_768_ = lean_ctor_get(v_a_500_, 1);
lean_inc_ref(v_fileMap_768_);
v_options_769_ = lean_ctor_get(v_a_500_, 2);
lean_inc_ref(v_options_769_);
v_currRecDepth_770_ = lean_ctor_get(v_a_500_, 3);
lean_inc(v_currRecDepth_770_);
v_maxRecDepth_771_ = lean_ctor_get(v_a_500_, 4);
lean_inc(v_maxRecDepth_771_);
v_ref_772_ = lean_ctor_get(v_a_500_, 5);
lean_inc(v_ref_772_);
v_currNamespace_773_ = lean_ctor_get(v_a_500_, 6);
lean_inc(v_currNamespace_773_);
v_openDecls_774_ = lean_ctor_get(v_a_500_, 7);
lean_inc(v_openDecls_774_);
v_initHeartbeats_775_ = lean_ctor_get(v_a_500_, 8);
lean_inc(v_initHeartbeats_775_);
v_maxHeartbeats_776_ = lean_ctor_get(v_a_500_, 9);
lean_inc(v_maxHeartbeats_776_);
v_quotContext_777_ = lean_ctor_get(v_a_500_, 10);
lean_inc(v_quotContext_777_);
v_currMacroScope_778_ = lean_ctor_get(v_a_500_, 11);
lean_inc(v_currMacroScope_778_);
v_diag_779_ = lean_ctor_get_uint8(v_a_500_, sizeof(void*)*14);
v_cancelTk_x3f_780_ = lean_ctor_get(v_a_500_, 12);
lean_inc(v_cancelTk_x3f_780_);
v_suppressElabErrors_781_ = lean_ctor_get_uint8(v_a_500_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_782_ = lean_ctor_get(v_a_500_, 13);
lean_inc_ref(v_inheritedTraceOptions_782_);
lean_dec_ref(v_a_500_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_nat_dec_eq(v_maxRecDepth_771_, v___x_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = lean_nat_dec_eq(v_currRecDepth_770_, v_maxRecDepth_771_);
if (v___x_826_ == 0)
{
goto v___jp_783_;
}
else
{
lean_object* v___x_827_; 
lean_dec_ref(v_inheritedTraceOptions_782_);
lean_dec(v_cancelTk_x3f_780_);
lean_dec(v_currMacroScope_778_);
lean_dec(v_quotContext_777_);
lean_dec(v_maxHeartbeats_776_);
lean_dec(v_initHeartbeats_775_);
lean_dec(v_openDecls_774_);
lean_dec(v_currNamespace_773_);
lean_dec(v_maxRecDepth_771_);
lean_dec(v_currRecDepth_770_);
lean_dec_ref(v_options_769_);
lean_dec_ref(v_fileMap_768_);
lean_dec_ref(v_fileName_767_);
lean_dec_ref(v_c_491_);
v___x_827_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_772_);
return v___x_827_;
}
}
else
{
goto v___jp_783_;
}
v___jp_503_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
v___jp_506_:
{
lean_object* v___x_514_; 
v___x_514_ = l_Int_Linear_Poly_updateOccs___redArg(v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec_ref(v___y_512_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v___x_514_);
v___x_515_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_516_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_515_, v___y_507_, v___y_509_);
return v___x_516_;
}
else
{
lean_dec_ref(v___y_507_);
return v___x_514_;
}
}
v___jp_517_:
{
if (lean_obj_tag(v___y_539_) == 1)
{
lean_object* v_val_540_; lean_object* v_p_541_; 
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_527_);
v_val_540_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v___y_539_);
v_p_541_ = lean_ctor_get(v_val_540_, 1);
lean_inc_ref(v_p_541_);
if (lean_obj_tag(v_p_541_) == 1)
{
lean_object* v_d_542_; lean_object* v_k_543_; lean_object* v_p_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_597_; 
v_d_542_ = lean_ctor_get(v_val_540_, 0);
v_k_543_ = lean_ctor_get(v_p_541_, 0);
v_p_544_ = lean_ctor_get(v_p_541_, 2);
v_isSharedCheck_597_ = !lean_is_exclusive(v_p_541_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_p_541_, 1);
lean_dec(v_unused_598_);
v___x_546_ = v_p_541_;
v_isShared_547_ = v_isSharedCheck_597_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_p_544_);
lean_inc(v_k_543_);
lean_dec(v_p_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_597_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_snd_551_; lean_object* v_fst_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_596_; 
v___x_548_ = lean_int_mul(v___y_528_, v_d_542_);
v___x_549_ = lean_int_mul(v_k_543_, v___y_531_);
v___x_550_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_548_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_548_);
v_snd_551_ = lean_ctor_get(v___x_550_, 1);
v_fst_552_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_596_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_552_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_595_; 
v_fst_556_ = lean_ctor_get(v_snd_551_, 0);
v_snd_557_ = lean_ctor_get(v_snd_551_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_snd_551_);
if (v_isSharedCheck_595_ == 0)
{
v___x_559_ = v_snd_551_;
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_inc(v_fst_556_);
lean_dec(v_snd_551_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_562_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_561_, v___y_526_, v___y_530_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec_ref(v___x_562_);
v___x_563_ = lean_int_mul(v_fst_556_, v_d_542_);
lean_dec(v_fst_556_);
lean_inc_ref(v___y_520_);
v___x_564_ = l_Int_Linear_Poly_mul(v___y_520_, v___x_563_);
lean_dec(v___x_563_);
v___x_565_ = lean_int_mul(v_snd_557_, v___y_531_);
lean_dec(v_snd_557_);
lean_inc_ref(v_p_544_);
v___x_566_ = l_Int_Linear_Poly_mul(v_p_544_, v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = lean_int_mul(v___y_531_, v_d_542_);
lean_dec(v___y_531_);
v___x_568_ = l_Int_Linear_Poly_combine(v___x_564_, v___x_566_);
lean_inc(v_fst_552_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v___x_568_);
lean_ctor_set(v___x_546_, 1, v___y_525_);
lean_ctor_set(v___x_546_, 0, v_fst_552_);
v___x_570_ = v___x_546_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_fst_552_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___y_525_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v___x_568_);
v___x_570_ = v_reuseFailAlloc_594_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
lean_inc(v_val_540_);
lean_inc_ref(v___y_522_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 4);
lean_ctor_set(v___x_559_, 1, v_val_540_);
lean_ctor_set(v___x_559_, 0, v___y_522_);
v___x_572_ = v___x_559_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_val_540_);
v___x_572_ = v_reuseFailAlloc_593_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_567_);
lean_ctor_set(v___x_573_, 1, v___x_570_);
lean_ctor_set(v___x_573_, 2, v___x_572_);
lean_inc_ref(v___y_533_);
v___x_574_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_573_, v___y_530_, v___y_529_, v___y_537_, v___y_518_, v___y_534_, v___y_538_, v___y_523_, v___y_536_, v___y_533_, v___y_524_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec_ref(v___x_574_);
v___x_575_ = l_Int_Linear_Poly_mul(v___y_520_, v_k_543_);
lean_dec(v_k_543_);
v___x_576_ = lean_int_neg(v___y_528_);
lean_dec(v___y_528_);
v___x_577_ = l_Int_Linear_Poly_mul(v_p_544_, v___x_576_);
lean_dec(v___x_576_);
v___x_578_ = l_Int_Linear_Poly_combine(v___x_575_, v___x_577_);
lean_inc(v_val_540_);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 5);
lean_ctor_set(v___x_554_, 1, v_val_540_);
lean_ctor_set(v___x_554_, 0, v___y_522_);
v___x_580_ = v___x_554_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_val_540_);
v___x_580_ = v_reuseFailAlloc_592_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v_val_540_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_589_ = lean_ctor_get(v_val_540_, 2);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_val_540_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_val_540_, 0);
lean_dec(v_unused_591_);
v___x_582_ = v_val_540_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_val_540_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 2, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_578_);
lean_ctor_set(v___x_582_, 0, v_fst_552_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fst_552_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___x_580_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v_c_491_ = v___x_585_;
v_a_492_ = v___y_530_;
v_a_493_ = v___y_529_;
v_a_494_ = v___y_537_;
v_a_495_ = v___y_518_;
v_a_496_ = v___y_534_;
v_a_497_ = v___y_538_;
v_a_498_ = v___y_523_;
v_a_499_ = v___y_536_;
v_a_500_ = v___y_533_;
v_a_501_ = v___y_524_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_554_);
lean_dec(v_fst_552_);
lean_dec_ref(v_p_544_);
lean_dec(v_k_543_);
lean_dec(v_val_540_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_520_);
return v___x_574_;
}
}
}
}
else
{
lean_del_object(v___x_559_);
lean_dec(v_snd_557_);
lean_dec(v_fst_556_);
lean_del_object(v___x_554_);
lean_dec(v_fst_552_);
lean_del_object(v___x_546_);
lean_dec_ref(v_p_544_);
lean_dec(v_k_543_);
lean_dec(v_val_540_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_531_);
lean_dec(v___y_528_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_520_);
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v___x_599_; 
lean_dec_ref(v_p_541_);
lean_dec(v___y_531_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_520_);
v___x_599_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_540_, v___y_530_, v___y_529_, v___y_537_, v___y_518_, v___y_534_, v___y_538_, v___y_523_, v___y_536_, v___y_533_, v___y_524_);
lean_dec_ref(v___y_533_);
return v___x_599_;
}
}
else
{
lean_object* v_options_600_; uint8_t v_hasTrace_601_; 
lean_dec(v___y_539_);
lean_dec(v___y_531_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_520_);
v_options_600_ = lean_ctor_get(v___y_533_, 2);
v_hasTrace_601_ = lean_ctor_get_uint8(v_options_600_, sizeof(void*)*1);
if (v_hasTrace_601_ == 0)
{
lean_dec_ref(v___y_522_);
v___y_507_ = v___y_527_;
v___y_508_ = v___y_535_;
v___y_509_ = v___y_530_;
v___y_510_ = v___y_523_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_533_;
v___y_513_ = v___y_524_;
goto v___jp_506_;
}
else
{
lean_object* v_inheritedTraceOptions_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_inheritedTraceOptions_602_ = lean_ctor_get(v___y_533_, 13);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_521_);
lean_inc_ref(v___y_532_);
lean_inc_ref(v___y_519_);
v___x_604_ = l_Lean_Name_mkStr4(v___y_519_, v___y_532_, v___y_521_, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_604_);
v___x_606_ = l_Lean_Name_append(v___x_605_, v___x_604_);
v___x_607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_602_, v_options_600_, v___x_606_);
lean_dec(v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v___x_604_);
lean_dec_ref(v___y_522_);
v___y_507_ = v___y_527_;
v___y_508_ = v___y_535_;
v___y_509_ = v___y_530_;
v___y_510_ = v___y_523_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_533_;
v___y_513_ = v___y_524_;
goto v___jp_506_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_522_, v___y_530_, v___y_533_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
v___x_610_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_604_, v_a_609_, v___y_523_, v___y_536_, v___y_533_, v___y_524_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_dec_ref(v___x_610_);
v___y_507_ = v___y_527_;
v___y_508_ = v___y_535_;
v___y_509_ = v___y_530_;
v___y_510_ = v___y_523_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_533_;
v___y_513_ = v___y_524_;
goto v___jp_506_;
}
else
{
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v___y_527_);
return v___x_610_;
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v___x_604_);
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v___y_527_);
v_a_611_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_608_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_608_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
}
v___jp_619_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_631_, v___y_639_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_dvds_643_; lean_object* v_size_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
v_dvds_643_ = lean_ctor_get(v_a_642_, 6);
lean_inc_ref(v_dvds_643_);
lean_dec(v_a_642_);
v_size_644_ = lean_ctor_get(v_dvds_643_, 2);
v___x_645_ = lean_box(0);
v___x_646_ = lean_nat_dec_lt(v___y_628_, v_size_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v_dvds_643_);
v___x_647_ = l_outOfBounds___redArg(v___x_645_);
v___y_518_ = v___y_634_;
v___y_519_ = v___y_622_;
v___y_520_ = v___y_621_;
v___y_521_ = v___y_624_;
v___y_522_ = v___y_625_;
v___y_523_ = v___y_637_;
v___y_524_ = v___y_640_;
v___y_525_ = v___y_628_;
v___y_526_ = v___y_630_;
v___y_527_ = v___y_620_;
v___y_528_ = v___y_623_;
v___y_529_ = v___y_632_;
v___y_530_ = v___y_631_;
v___y_531_ = v___y_626_;
v___y_532_ = v___y_627_;
v___y_533_ = v___y_639_;
v___y_534_ = v___y_635_;
v___y_535_ = v___y_629_;
v___y_536_ = v___y_638_;
v___y_537_ = v___y_633_;
v___y_538_ = v___y_636_;
v___y_539_ = v___x_647_;
goto v___jp_517_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentArray_get_x21___redArg(v___x_645_, v_dvds_643_, v___y_628_);
lean_dec_ref(v_dvds_643_);
v___y_518_ = v___y_634_;
v___y_519_ = v___y_622_;
v___y_520_ = v___y_621_;
v___y_521_ = v___y_624_;
v___y_522_ = v___y_625_;
v___y_523_ = v___y_637_;
v___y_524_ = v___y_640_;
v___y_525_ = v___y_628_;
v___y_526_ = v___y_630_;
v___y_527_ = v___y_620_;
v___y_528_ = v___y_623_;
v___y_529_ = v___y_632_;
v___y_530_ = v___y_631_;
v___y_531_ = v___y_626_;
v___y_532_ = v___y_627_;
v___y_533_ = v___y_639_;
v___y_534_ = v___y_635_;
v___y_535_ = v___y_629_;
v___y_536_ = v___y_638_;
v___y_537_ = v___y_633_;
v___y_538_ = v___y_636_;
v___y_539_ = v___x_648_;
goto v___jp_517_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_620_);
v_a_649_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_641_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_641_);
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
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_491_);
lean_inc_ref(v___y_692_);
v___x_695_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_694_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_d_697_; lean_object* v_p_698_; uint8_t v___x_699_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v_d_697_ = lean_ctor_get(v_a_696_, 0);
v_p_698_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_d_697_);
v___x_699_ = l_Int_Linear_Poly_isUnsatDvd(v_d_697_, v_p_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_696_);
if (v___x_700_ == 0)
{
if (lean_obj_tag(v_p_698_) == 1)
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_p_703_; lean_object* v___x_704_; 
lean_inc_ref(v_p_698_);
lean_inc(v_d_697_);
v_k_701_ = lean_ctor_get(v_p_698_, 0);
lean_inc(v_k_701_);
v_v_702_ = lean_ctor_get(v_p_698_, 1);
lean_inc(v_v_702_);
v_p_703_ = lean_ctor_get(v_p_698_, 2);
lean_inc_ref(v_p_703_);
lean_inc(v_a_696_);
v___x_704_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_696_, v___y_684_, v___y_692_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___f_706_; lean_object* v___f_707_; uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
lean_inc_n(v_v_702_, 2);
lean_inc(v_a_696_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_706_, 0, v_a_696_);
lean_closure_set(v___f_706_, 1, v_v_702_);
v___f_707_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_707_, 0, v_v_702_);
v___x_708_ = 0;
v___x_709_ = lean_unbox(v_a_705_);
lean_dec(v_a_705_);
v___x_710_ = l_Lean_instBEqLBool_beq(v___x_709_, v___x_708_);
if (v___x_710_ == 0)
{
v___y_620_ = v___f_706_;
v___y_621_ = v_p_703_;
v___y_622_ = v___y_681_;
v___y_623_ = v_k_701_;
v___y_624_ = v___y_682_;
v___y_625_ = v_a_696_;
v___y_626_ = v_d_697_;
v___y_627_ = v___y_683_;
v___y_628_ = v_v_702_;
v___y_629_ = v_p_698_;
v___y_630_ = v___f_707_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
goto v___jp_619_;
}
else
{
lean_object* v___x_711_; 
lean_inc(v_v_702_);
v___x_711_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_702_, v___y_684_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_dec_ref(v___x_711_);
v___y_620_ = v___f_706_;
v___y_621_ = v_p_703_;
v___y_622_ = v___y_681_;
v___y_623_ = v_k_701_;
v___y_624_ = v___y_682_;
v___y_625_ = v_a_696_;
v___y_626_ = v_d_697_;
v___y_627_ = v___y_683_;
v___y_628_ = v_v_702_;
v___y_629_ = v_p_698_;
v___y_630_ = v___f_707_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
goto v___jp_619_;
}
else
{
lean_dec_ref(v___f_707_);
lean_dec_ref(v___f_706_);
lean_dec_ref(v_p_703_);
lean_dec(v_v_702_);
lean_dec(v_k_701_);
lean_dec_ref(v_p_698_);
lean_dec(v_d_697_);
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
return v___x_711_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_p_703_);
lean_dec(v_v_702_);
lean_dec(v_k_701_);
lean_dec_ref(v_p_698_);
lean_dec(v_d_697_);
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
v_a_712_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_704_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_704_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_696_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec_ref(v___y_692_);
return v___x_720_;
}
}
else
{
lean_object* v_options_721_; uint8_t v_hasTrace_722_; 
v_options_721_ = lean_ctor_get(v___y_692_, 2);
v_hasTrace_722_ = lean_ctor_get_uint8(v_options_721_, sizeof(void*)*1);
if (v_hasTrace_722_ == 0)
{
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
goto v___jp_503_;
}
else
{
lean_object* v_inheritedTraceOptions_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_inheritedTraceOptions_723_ = lean_ctor_get(v___y_692_, 13);
v___x_724_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_681_);
v___x_725_ = l_Lean_Name_mkStr4(v___y_681_, v___y_683_, v___y_682_, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_725_);
v___x_727_ = l_Lean_Name_append(v___x_726_, v___x_725_);
v___x_728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_723_, v_options_721_, v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
goto v___jp_503_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_696_, v___y_684_, v___y_692_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_725_, v_a_730_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec_ref(v___y_692_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref(v___x_731_);
goto v___jp_503_;
}
else
{
return v___x_731_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v___x_725_);
lean_dec_ref(v___y_692_);
v_a_732_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_729_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_729_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_740_; uint8_t v_hasTrace_741_; 
v_options_740_ = lean_ctor_get(v___y_692_, 2);
v_hasTrace_741_ = lean_ctor_get_uint8(v_options_740_, sizeof(void*)*1);
if (v_hasTrace_741_ == 0)
{
v___y_658_ = v_a_696_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
goto v___jp_657_;
}
else
{
lean_object* v_inheritedTraceOptions_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_inheritedTraceOptions_742_ = lean_ctor_get(v___y_692_, 13);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_681_);
v___x_744_ = l_Lean_Name_mkStr4(v___y_681_, v___y_683_, v___y_682_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_744_);
v___x_746_ = l_Lean_Name_append(v___x_745_, v___x_744_);
v___x_747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_742_, v_options_740_, v___x_746_);
lean_dec(v___x_746_);
if (v___x_747_ == 0)
{
lean_dec(v___x_744_);
v___y_658_ = v_a_696_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
goto v___jp_657_;
}
else
{
lean_object* v___x_748_; 
lean_inc(v_a_696_);
v___x_748_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_696_, v___y_684_, v___y_692_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_744_, v_a_749_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref(v___x_750_);
v___y_658_ = v_a_696_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
goto v___jp_657_;
}
else
{
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
return v___x_750_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_744_);
lean_dec(v_a_696_);
lean_dec_ref(v___y_692_);
v_a_751_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_748_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_748_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v___y_692_);
v_a_759_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_695_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_695_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_currRecDepth_770_, v___x_784_);
lean_dec(v_currRecDepth_770_);
lean_inc_ref(v_inheritedTraceOptions_782_);
lean_inc_ref(v_options_769_);
v___x_786_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_786_, 0, v_fileName_767_);
lean_ctor_set(v___x_786_, 1, v_fileMap_768_);
lean_ctor_set(v___x_786_, 2, v_options_769_);
lean_ctor_set(v___x_786_, 3, v___x_785_);
lean_ctor_set(v___x_786_, 4, v_maxRecDepth_771_);
lean_ctor_set(v___x_786_, 5, v_ref_772_);
lean_ctor_set(v___x_786_, 6, v_currNamespace_773_);
lean_ctor_set(v___x_786_, 7, v_openDecls_774_);
lean_ctor_set(v___x_786_, 8, v_initHeartbeats_775_);
lean_ctor_set(v___x_786_, 9, v_maxHeartbeats_776_);
lean_ctor_set(v___x_786_, 10, v_quotContext_777_);
lean_ctor_set(v___x_786_, 11, v_currMacroScope_778_);
lean_ctor_set(v___x_786_, 12, v_cancelTk_x3f_780_);
lean_ctor_set(v___x_786_, 13, v_inheritedTraceOptions_782_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*14, v_diag_779_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*14 + 1, v_suppressElabErrors_781_);
v___x_787_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_492_, v___x_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_815_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_815_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_815_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_815_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
uint8_t v___x_792_; 
v___x_792_ = lean_unbox(v_a_788_);
lean_dec(v_a_788_);
if (v___x_792_ == 0)
{
uint8_t v_hasTrace_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_790_);
v_hasTrace_793_ = lean_ctor_get_uint8(v_options_769_, sizeof(void*)*1);
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_796_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_793_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_782_);
lean_dec_ref(v_options_769_);
v___y_681_ = v___x_794_;
v___y_682_ = v___x_796_;
v___y_683_ = v___x_795_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v___x_786_;
v___y_693_ = v_a_501_;
goto v___jp_680_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_798_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_782_, v_options_769_, v___x_798_);
lean_dec_ref(v_options_769_);
lean_dec_ref(v_inheritedTraceOptions_782_);
if (v___x_799_ == 0)
{
v___y_681_ = v___x_794_;
v___y_682_ = v___x_796_;
v___y_683_ = v___x_795_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v___x_786_;
v___y_693_ = v_a_501_;
goto v___jp_680_;
}
else
{
lean_object* v___x_800_; 
lean_inc_ref(v_c_491_);
v___x_800_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_491_, v_a_492_, v___x_786_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_797_, v_a_801_, v_a_498_, v_a_499_, v___x_786_, v_a_501_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_dec_ref(v___x_802_);
v___y_681_ = v___x_794_;
v___y_682_ = v___x_796_;
v___y_683_ = v___x_795_;
v___y_684_ = v_a_492_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v___x_786_;
v___y_693_ = v_a_501_;
goto v___jp_680_;
}
else
{
lean_dec_ref(v___x_786_);
lean_dec_ref(v_c_491_);
return v___x_802_;
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___x_786_);
lean_dec_ref(v_c_491_);
v_a_803_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_800_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec_ref(v___x_786_);
lean_dec_ref(v_inheritedTraceOptions_782_);
lean_dec_ref(v_options_769_);
lean_dec_ref(v_c_491_);
v___x_811_ = lean_box(0);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_811_);
v___x_813_ = v___x_790_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
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
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v___x_786_);
lean_dec_ref(v_inheritedTraceOptions_782_);
lean_dec_ref(v_options_769_);
lean_dec_ref(v_c_491_);
v_a_816_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_787_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_787_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec(v_a_829_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_d_853_; lean_object* v_p_854_; lean_object* v___x_855_; 
v_d_853_ = lean_ctor_get(v_c_841_, 0);
v_p_854_ = lean_ctor_get(v_c_841_, 1);
lean_inc_ref(v_p_854_);
v___x_855_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_854_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
if (lean_obj_tag(v_a_856_) == 1)
{
lean_object* v_val_857_; lean_object* v_snd_858_; lean_object* v_fst_859_; lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc(v_d_853_);
v_val_857_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref(v_a_856_);
v_snd_858_ = lean_ctor_get(v_val_857_, 1);
lean_inc(v_snd_858_);
v_fst_859_ = lean_ctor_get(v_val_857_, 0);
lean_inc(v_fst_859_);
lean_dec(v_val_857_);
v_fst_860_ = lean_ctor_get(v_snd_858_, 0);
lean_inc(v_fst_860_);
v_snd_861_ = lean_ctor_get(v_snd_858_, 1);
lean_inc(v_snd_861_);
lean_dec(v_snd_858_);
v___x_862_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_862_, 0, v_c_841_);
lean_ctor_set(v___x_862_, 1, v_fst_859_);
lean_ctor_set(v___x_862_, 2, v_fst_860_);
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v_d_853_);
lean_ctor_set(v___x_863_, 1, v_snd_861_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
lean_inc_ref(v_a_850_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_863_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; 
lean_dec(v_a_856_);
lean_inc_ref(v_a_850_);
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_865_;
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_c_841_);
v_a_866_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_855_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_a_875_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6));
v___x_901_ = l_Lean_mkConst(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_920_; 
lean_inc_ref(v_e_905_);
v___x_920_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_905_, v_a_913_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_1054_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_1054_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_1054_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = l_Lean_Expr_cleanupAnnotations(v_a_921_);
v___x_931_ = l_Lean_Expr_isApp(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_930_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_arg_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc_ref(v_arg_932_);
v___x_933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_930_);
v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_933_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_arg_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc_ref(v_arg_935_);
v___x_936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
v___x_937_ = l_Lean_Expr_isApp(v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_936_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_arg_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_arg_938_);
v___x_939_ = l_Lean_Expr_appFnCleanup___redArg(v___x_936_);
v___x_940_ = l_Lean_Expr_isApp(v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = l_Lean_Expr_appFnCleanup___redArg(v___x_939_);
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_943_ = l_Lean_Expr_isConstOf(v___x_941_, v___x_942_);
lean_dec_ref(v___x_941_);
if (v___x_943_ == 0)
{
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v___x_944_; 
lean_del_object(v___x_923_);
v___x_944_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_938_, v_a_913_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1045_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_1045_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1045_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
uint8_t v___x_949_; 
v___x_949_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v___x_950_ = lean_box(0);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_954_; 
lean_del_object(v___x_947_);
lean_inc_ref(v_arg_935_);
v___x_954_ = l_Lean_Meta_getIntValue_x3f(v_arg_935_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref(v___x_954_);
if (lean_obj_tag(v_a_955_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1021_; 
v_val_956_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_958_ = v_a_955_;
v_isShared_959_ = v_isSharedCheck_1021_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v_a_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1021_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; 
lean_inc_ref(v_e_905_);
v___x_960_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_905_, v_a_906_, v_a_910_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_unbox(v_a_961_);
lean_dec(v_a_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_inc_ref(v_e_905_);
v___x_963_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_905_, v_a_906_, v_a_910_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_989_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_989_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_989_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_989_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
v___x_968_ = lean_unbox(v_a_964_);
lean_dec(v_a_964_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v___x_969_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_973_; 
lean_del_object(v___x_966_);
lean_inc_ref(v_e_905_);
v___x_973_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
v___x_976_ = l_Lean_eagerReflBoolTrue;
v___x_977_ = l_Lean_Meta_mkOfEqFalseCore(v_e_905_, v_a_974_);
v___x_978_ = l_Lean_mkApp4(v___x_975_, v_arg_935_, v_arg_932_, v___x_976_, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = l_Lean_Meta_Grind_pushNewFact(v___x_978_, v___x_979_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_981_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_973_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_973_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_990_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_963_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_963_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v___x_998_; 
lean_dec_ref(v_arg_935_);
v___x_998_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_932_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
lean_ctor_set(v___x_958_, 0, v_e_905_);
v___x_1001_ = v___x_958_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_e_905_);
v___x_1001_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_val_956_);
lean_ctor_set(v___x_1002_, 1, v_a_999_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
v___x_1003_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1002_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_1003_;
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_dec_ref(v_e_905_);
v_a_1005_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_998_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_998_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1013_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_960_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_960_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_a_955_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
v___x_1022_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_910_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; uint8_t v___x_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = lean_unbox(v_a_1023_);
lean_dec(v_a_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v_e_905_);
goto v___jp_917_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1026_ = l_Lean_indentExpr(v_e_905_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Meta_Sym_reportIssue(v___x_1027_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_dec_ref(v___x_1028_);
goto v___jp_917_;
}
else
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_e_905_);
v_a_1029_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1022_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1022_);
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
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1037_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_954_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_954_);
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
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1046_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_944_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_944_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
}
}
v___jp_925_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_e_905_);
v_a_1055_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_920_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_920_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
v___jp_917_:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_nat_to_int(v_a_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1085_ = l_Lean_mkConst(v___x_1084_, v___x_1083_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1094_ = l_Lean_mkConst(v___x_1093_, v___x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
lean_inc_ref(v_e_1095_);
v___x_1113_ = l_Lean_Expr_cleanupAnnotations(v_e_1095_);
v___x_1114_ = l_Lean_Expr_isApp(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_arg_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc_ref(v_arg_1115_);
v___x_1116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1113_);
v___x_1117_ = l_Lean_Expr_isApp(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_arg_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc_ref(v_arg_1118_);
v___x_1119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1116_);
v___x_1120_ = l_Lean_Expr_isApp(v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_arg_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc_ref(v_arg_1121_);
v___x_1122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1119_);
v___x_1123_ = l_Lean_Expr_isApp(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1122_);
v___x_1125_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1126_ = l_Lean_Expr_isConstOf(v___x_1124_, v___x_1125_);
lean_dec_ref(v___x_1124_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1121_, v_a_1103_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1259_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1259_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1259_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v___x_1133_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_object* v___x_1137_; 
lean_del_object(v___x_1130_);
v___x_1137_ = l_Lean_Meta_getNatValue_x3f(v_arg_1118_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref(v___x_1137_);
if (lean_obj_tag(v_a_1138_) == 1)
{
lean_object* v_val_1139_; lean_object* v___x_1140_; 
v_val_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref(v_a_1138_);
lean_inc_ref(v_e_1095_);
v___x_1140_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1095_, v_a_1096_, v_a_1100_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; uint8_t v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v_val_1139_);
lean_inc_ref(v_e_1095_);
v___x_1143_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1095_, v_a_1096_, v_a_1100_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1168_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v___x_1149_ = lean_box(0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1153_; 
lean_del_object(v___x_1146_);
lean_inc_ref(v_e_1095_);
v___x_1153_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1156_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1095_, v_a_1154_);
v___x_1157_ = l_Lean_mkApp3(v___x_1155_, v_arg_1118_, v_arg_1115_, v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l_Lean_Meta_Grind_pushNewFact(v___x_1157_, v___x_1158_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1160_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1153_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1153_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1169_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1143_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1143_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v___x_1177_; 
lean_inc_ref(v_arg_1118_);
v___x_1177_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1118_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v_fst_1179_ = lean_ctor_get(v_a_1178_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v_a_1178_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_a_1178_);
lean_inc_ref(v_arg_1115_);
v___x_1181_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1115_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref(v___x_1181_);
v_fst_1183_ = lean_ctor_get(v_a_1182_, 0);
lean_inc(v_fst_1183_);
v_snd_1184_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_snd_1184_);
lean_dec(v_a_1182_);
v___x_1185_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1185_);
lean_inc(v_fst_1183_);
v___x_1187_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1183_, v_a_1186_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l_Int_Linear_Expr_norm(v_a_1188_);
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1191_ = l_Lean_mkApp6(v___x_1190_, v_arg_1118_, v_arg_1115_, v_fst_1179_, v_fst_1183_, v_snd_1180_, v_snd_1184_);
lean_inc(v_val_1139_);
v___x_1192_ = lean_nat_to_int(v_val_1139_);
v___x_1193_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1193_, 0, v_e_1095_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v_val_1139_);
lean_ctor_set(v___x_1193_, 3, v_a_1188_);
v___x_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1189_);
lean_ctor_set(v___x_1194_, 2, v___x_1193_);
v___x_1195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1194_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1195_;
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_snd_1184_);
lean_dec(v_fst_1183_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1196_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1187_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1187_);
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
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_snd_1184_);
lean_dec(v_fst_1183_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1204_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1185_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1185_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1212_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1181_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1181_);
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
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1220_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1177_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1177_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1228_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1140_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1140_);
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
lean_object* v___x_1236_; 
lean_dec(v_a_1138_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
v___x_1236_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1100_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; uint8_t v___x_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = lean_unbox(v_a_1237_);
lean_dec(v_a_1237_);
if (v___x_1238_ == 0)
{
lean_dec_ref(v_e_1095_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1240_ = l_Lean_indentExpr(v_e_1095_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_Meta_Sym_reportIssue(v___x_1241_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref(v___x_1242_);
goto v___jp_1110_;
}
else
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_e_1095_);
v_a_1243_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1236_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1236_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1251_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1137_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1137_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1260_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1127_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1127_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1286_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1340_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1340_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1340_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
uint8_t v_lia_1300_; 
v_lia_1300_ = lean_ctor_get_uint8(v_a_1296_, sizeof(void*)*13 + 23);
lean_dec(v_a_1296_);
if (v_lia_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_dec_ref(v_e_1283_);
v___x_1301_ = lean_box(0);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
else
{
lean_object* v___x_1305_; 
lean_del_object(v___x_1298_);
lean_inc_ref(v_e_1283_);
v___x_1305_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1283_, v_a_1291_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1331_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = l_Lean_Expr_cleanupAnnotations(v_a_1306_);
v___x_1316_ = l_Lean_Expr_isApp(v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v___x_1315_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1315_);
v___x_1318_ = l_Lean_Expr_isApp(v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1317_);
v___x_1320_ = l_Lean_Expr_isApp(v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1319_);
v___x_1322_ = l_Lean_Expr_isApp(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v_arg_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_arg_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc_ref(v_arg_1323_);
v___x_1324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1321_);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1326_ = l_Lean_Expr_isConstOf(v___x_1324_, v___x_1325_);
lean_dec_ref(v___x_1324_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_del_object(v___x_1308_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1328_ = l_Lean_Expr_isConstOf(v_arg_1323_, v___x_1327_);
lean_dec_ref(v_arg_1323_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1330_;
}
}
}
}
}
}
v___jp_1310_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1313_ = v___x_1308_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_e_1283_);
v_a_1332_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1305_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1305_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_e_1283_);
v_a_1341_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1295_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1295_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1364_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1365_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1363_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return v_res_1367_;
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
