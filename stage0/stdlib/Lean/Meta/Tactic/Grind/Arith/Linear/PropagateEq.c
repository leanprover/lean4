// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.Linear.Den import Lean.Meta.Tactic.Grind.Arith.Linear.Reify import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 1, 87, 68, 102, 24, 231, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value),LEAN_SCALAR_PTR_LITERAL(206, 233, 164, 186, 216, 210, 242, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq.0.Lean.Meta.Grind.Arith.Linear.EqCnstr.norm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1;
static const lean_array_object l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ignored"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 67, 1, 106, 4, 67, 211, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 205, 246, 167, 183, 132, 208, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1;
static const lean_array_object l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">> "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 219, 223, 129, 16, 82, 214, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 54, 186, 23, 232, 175, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_21_, v___y_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* v_cls_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_cls_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec(v___y_37_);
lean_dec(v___y_36_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(lean_object* v_msgData_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; lean_object* v_env_56_; lean_object* v___x_57_; lean_object* v_mctx_58_; lean_object* v_lctx_59_; lean_object* v_options_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_55_ = lean_st_ref_get(v___y_53_);
v_env_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref(v_env_56_);
lean_dec(v___x_55_);
v___x_57_ = lean_st_ref_get(v___y_51_);
v_mctx_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_mctx_58_);
lean_dec(v___x_57_);
v_lctx_59_ = lean_ctor_get(v___y_50_, 2);
v_options_60_ = lean_ctor_get(v___y_52_, 2);
lean_inc_ref(v_options_60_);
lean_inc_ref(v_lctx_59_);
v___x_61_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_61_, 0, v_env_56_);
lean_ctor_set(v___x_61_, 1, v_mctx_58_);
lean_ctor_set(v___x_61_, 2, v_lctx_59_);
lean_ctor_set(v___x_61_, 3, v_options_60_);
v___x_62_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_msgData_49_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6___boxed(lean_object* v_msgData_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(v_msgData_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_70_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_71_; double v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_float_of_nat(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(lean_object* v_cls_76_, lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_ref_83_; lean_object* v___x_84_; lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_129_; 
v_ref_83_ = lean_ctor_get(v___y_80_, 5);
v___x_84_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(v_msg_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_129_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_129_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_129_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v_traceState_90_; lean_object* v_env_91_; lean_object* v_nextMacroScope_92_; lean_object* v_ngen_93_; lean_object* v_auxDeclNGen_94_; lean_object* v_cache_95_; lean_object* v_messages_96_; lean_object* v_infoState_97_; lean_object* v_snapshotTasks_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_128_; 
v___x_89_ = lean_st_ref_take(v___y_81_);
v_traceState_90_ = lean_ctor_get(v___x_89_, 4);
v_env_91_ = lean_ctor_get(v___x_89_, 0);
v_nextMacroScope_92_ = lean_ctor_get(v___x_89_, 1);
v_ngen_93_ = lean_ctor_get(v___x_89_, 2);
v_auxDeclNGen_94_ = lean_ctor_get(v___x_89_, 3);
v_cache_95_ = lean_ctor_get(v___x_89_, 5);
v_messages_96_ = lean_ctor_get(v___x_89_, 6);
v_infoState_97_ = lean_ctor_get(v___x_89_, 7);
v_snapshotTasks_98_ = lean_ctor_get(v___x_89_, 8);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_128_ == 0)
{
v___x_100_ = v___x_89_;
v_isShared_101_ = v_isSharedCheck_128_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_snapshotTasks_98_);
lean_inc(v_infoState_97_);
lean_inc(v_messages_96_);
lean_inc(v_cache_95_);
lean_inc(v_traceState_90_);
lean_inc(v_auxDeclNGen_94_);
lean_inc(v_ngen_93_);
lean_inc(v_nextMacroScope_92_);
lean_inc(v_env_91_);
lean_dec(v___x_89_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_128_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint64_t v_tid_102_; lean_object* v_traces_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_127_; 
v_tid_102_ = lean_ctor_get_uint64(v_traceState_90_, sizeof(void*)*1);
v_traces_103_ = lean_ctor_get(v_traceState_90_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_traceState_90_);
if (v_isSharedCheck_127_ == 0)
{
v___x_105_ = v_traceState_90_;
v_isShared_106_ = v_isSharedCheck_127_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_traces_103_);
lean_dec(v_traceState_90_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_127_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; double v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0);
v___x_109_ = 0;
v___x_110_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1));
v___x_111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_111_, 0, v_cls_76_);
lean_ctor_set(v___x_111_, 1, v___x_107_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
lean_ctor_set_float(v___x_111_, sizeof(void*)*3, v___x_108_);
lean_ctor_set_float(v___x_111_, sizeof(void*)*3 + 8, v___x_108_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*3 + 16, v___x_109_);
v___x_112_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2));
v___x_113_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v_a_85_);
lean_ctor_set(v___x_113_, 2, v___x_112_);
lean_inc(v_ref_83_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_ref_83_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = l_Lean_PersistentArray_push___redArg(v_traces_103_, v___x_114_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_115_);
v___x_117_ = v___x_105_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_115_);
lean_ctor_set_uint64(v_reuseFailAlloc_126_, sizeof(void*)*1, v_tid_102_);
v___x_117_ = v_reuseFailAlloc_126_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v___x_117_);
v___x_119_ = v___x_100_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_env_91_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_nextMacroScope_92_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_ngen_93_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_auxDeclNGen_94_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_125_, 5, v_cache_95_);
lean_ctor_set(v_reuseFailAlloc_125_, 6, v_messages_96_);
lean_ctor_set(v_reuseFailAlloc_125_, 7, v_infoState_97_);
lean_ctor_set(v_reuseFailAlloc_125_, 8, v_snapshotTasks_98_);
v___x_119_ = v_reuseFailAlloc_125_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = lean_st_ref_set(v___y_81_, v___x_119_);
v___x_121_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_121_);
v___x_123_ = v___x_87_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___boxed(lean_object* v_cls_130_, lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_130_, v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(lean_object* v_a_141_, lean_object* v_b_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_171_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_171_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_171_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_171_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_type_160_; lean_object* v_u_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v_type_160_ = lean_ctor_get(v_a_156_, 2);
lean_inc_ref(v_type_160_);
v_u_161_ = lean_ctor_get(v_a_156_, 3);
lean_inc(v_u_161_);
lean_dec(v_a_156_);
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1));
v___x_163_ = l_Lean_Level_succ___override(v_u_161_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_mkConst(v___x_162_, v___x_165_);
v___x_167_ = l_Lean_mkApp3(v___x_166_, v_type_160_, v_a_141_, v_b_142_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_167_);
v___x_169_ = v___x_158_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec_ref(v_b_142_);
lean_dec_ref(v_a_141_);
v_a_172_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_155_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_155_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___boxed(lean_object* v_a_180_, lean_object* v_b_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(v_a_180_, v_b_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec(v___y_183_);
lean_dec(v___y_182_);
return v_res_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_to_int(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object* v_k_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_212_ = lean_int_dec_eq(v_k_197_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_234_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_234_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_234_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_234_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_vars_220_; lean_object* v_zsmulFn_221_; lean_object* v_size_222_; lean_object* v___x_223_; lean_object* v___y_225_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_vars_220_ = lean_ctor_get(v_a_216_, 30);
lean_inc_ref(v_vars_220_);
lean_dec(v_a_216_);
v_zsmulFn_221_ = lean_ctor_get(v_a_214_, 23);
lean_inc_ref(v_zsmulFn_221_);
lean_dec(v_a_214_);
v_size_222_ = lean_ctor_get(v_vars_220_, 2);
v___x_223_ = l_Lean_mkIntLit(v_k_197_);
v___x_230_ = l_Lean_instInhabitedExpr;
v___x_231_ = lean_nat_dec_lt(v_x_198_, v_size_222_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec_ref(v_vars_220_);
v___x_232_ = l_outOfBounds___redArg(v___x_230_);
v___y_225_ = v___x_232_;
goto v___jp_224_;
}
else
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentArray_get_x21___redArg(v___x_230_, v_vars_220_, v_x_198_);
v___y_225_ = v___x_233_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = l_Lean_mkAppB(v_zsmulFn_221_, v___x_223_, v___y_225_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_226_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_214_);
v_a_235_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_215_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_215_);
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
v_a_243_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_213_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_213_);
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
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_268_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_268_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_268_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_268_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_vars_256_; lean_object* v_size_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_vars_256_ = lean_ctor_get(v_a_252_, 30);
lean_inc_ref(v_vars_256_);
lean_dec(v_a_252_);
v_size_257_ = lean_ctor_get(v_vars_256_, 2);
v___x_258_ = l_Lean_instInhabitedExpr;
v___x_259_ = lean_nat_dec_lt(v_x_198_, v_size_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec_ref(v_vars_256_);
v___x_260_ = l_outOfBounds___redArg(v___x_258_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_260_);
v___x_262_ = v___x_254_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = l_Lean_PersistentArray_get_x21___redArg(v___x_258_, v_vars_256_, v_x_198_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_264_);
v___x_266_ = v___x_254_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_251_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_251_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object* v_k_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(v_k_277_, v_x_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec(v___y_280_);
lean_dec(v___y_279_);
lean_dec(v_x_278_);
lean_dec(v_k_277_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object* v_p_292_, lean_object* v_acc_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
if (lean_obj_tag(v_p_292_) == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v_acc_293_);
return v___x_306_;
}
else
{
lean_object* v_k_307_; lean_object* v_v_308_; lean_object* v_p_309_; lean_object* v___x_310_; 
v_k_307_ = lean_ctor_get(v_p_292_, 0);
v_v_308_ = lean_ctor_get(v_p_292_, 1);
v_p_309_ = lean_ctor_get(v_p_292_, 2);
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_310_);
v___x_312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(v_k_307_, v_v_308_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_addFn_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_addFn_314_ = lean_ctor_get(v_a_311_, 22);
lean_inc_ref(v_addFn_314_);
lean_dec(v_a_311_);
v___x_315_ = l_Lean_mkAppB(v_addFn_314_, v_acc_293_, v_a_313_);
v_p_292_ = v_p_309_;
v_acc_293_ = v___x_315_;
goto _start;
}
else
{
lean_dec(v_a_311_);
lean_dec_ref(v_acc_293_);
return v___x_312_;
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_acc_293_);
v_a_317_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_310_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_310_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object* v_p_325_, lean_object* v_acc_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(v_p_325_, v_acc_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
lean_dec(v___y_327_);
lean_dec(v_p_325_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* v_p_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
if (lean_obj_tag(v_p_340_) == 0)
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_362_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_362_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_362_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_362_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_zero_358_; lean_object* v___x_360_; 
v_zero_358_ = lean_ctor_get(v_a_354_, 17);
lean_inc_ref(v_zero_358_);
lean_dec(v_a_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v_zero_358_);
v___x_360_ = v___x_356_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_zero_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_353_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_353_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v_p_373_; lean_object* v___x_374_; 
v_k_371_ = lean_ctor_get(v_p_340_, 0);
v_v_372_ = lean_ctor_get(v_p_340_, 1);
v_p_373_ = lean_ctor_get(v_p_340_, 2);
v___x_374_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(v_k_371_, v_v_372_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v___x_374_);
v___x_376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(v_p_373_, v_a_375_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_376_;
}
else
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* v_p_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v___y_378_);
lean_dec(v_p_377_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_c_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_p_404_; lean_object* v___x_405_; 
v_p_404_ = lean_ctor_get(v_c_391_, 0);
v___x_405_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_404_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_ofNatZero_409_; lean_object* v___x_410_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v_ofNatZero_409_ = lean_ctor_get(v_a_408_, 18);
lean_inc_ref(v_ofNatZero_409_);
lean_dec(v_a_408_);
v___x_410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(v_a_406_, v_ofNatZero_409_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_410_;
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_406_);
v_a_411_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_407_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_c_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v_c_419_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v_natZero_445_; lean_object* v_intZero_446_; 
v_natZero_445_ = lean_unsigned_to_nat(0u);
v_intZero_446_ = lean_nat_to_int(v_natZero_445_);
return v_intZero_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_611_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_611_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_611_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_611_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
if (lean_obj_tag(v_a_462_) == 1)
{
lean_object* v_val_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_606_; 
lean_del_object(v___x_464_);
v_val_466_ = lean_ctor_get(v_a_462_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_606_ == 0)
{
v___x_468_ = v_a_462_;
v_isShared_469_ = v_isSharedCheck_606_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_val_466_);
lean_dec(v_a_462_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_606_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_snd_470_; lean_object* v_snd_471_; lean_object* v_fst_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_604_; 
v_snd_470_ = lean_ctor_get(v_val_466_, 1);
lean_inc(v_snd_470_);
v_snd_471_ = lean_ctor_get(v_snd_470_, 1);
lean_inc(v_snd_471_);
v_fst_472_ = lean_ctor_get(v_val_466_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_val_466_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v_val_466_, 1);
lean_dec(v_unused_605_);
v___x_474_ = v_val_466_;
v_isShared_475_ = v_isSharedCheck_604_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_fst_472_);
lean_dec(v_val_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_604_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_fst_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_602_; 
v_fst_476_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_snd_470_, 1);
lean_dec(v_unused_603_);
v___x_478_ = v_snd_470_;
v_isShared_479_ = v_isSharedCheck_602_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_fst_476_);
lean_dec(v_snd_470_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_602_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_p_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_601_; 
v_p_480_ = lean_ctor_get(v_snd_471_, 0);
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_482_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_481_, v_a_458_);
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_601_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_601_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_601_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_505_; 
v___x_487_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_480_, v_fst_476_);
lean_inc(v_p_448_);
v___x_488_ = l_Lean_Grind_Linarith_Poly_mul(v_p_448_, v___x_487_);
v___x_489_ = lean_int_neg(v_fst_472_);
lean_inc(v_p_480_);
v___x_490_ = l_Lean_Grind_Linarith_Poly_mul(v_p_480_, v___x_489_);
lean_dec(v___x_489_);
v___x_491_ = l_Lean_Grind_Linarith_Poly_combine(v___x_488_, v___x_490_);
v___x_505_ = lean_unbox(v_a_483_);
lean_dec(v_a_483_);
if (v___x_505_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v_fst_472_);
lean_dec(v_p_448_);
goto v___jp_492_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_p_448_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_476_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_snd_471_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___x_491_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___x_534_; lean_object* v___y_536_; lean_object* v_intZero_558_; uint8_t v_isNeg_559_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_MessageData_ofExpr(v_a_507_);
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_514_);
lean_ctor_set(v___x_534_, 1, v___x_515_);
v_intZero_558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v_isNeg_559_ = lean_int_dec_lt(v_fst_472_, v_intZero_558_);
if (v_isNeg_559_ == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_nat_abs(v_fst_472_);
lean_dec(v_fst_472_);
v___x_561_ = l_Nat_reprFast(v_a_560_);
v___y_536_ = v___x_561_;
goto v___jp_535_;
}
else
{
lean_object* v_abs_562_; lean_object* v_one_563_; lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_abs_562_ = lean_nat_abs(v_fst_472_);
lean_dec(v_fst_472_);
v_one_563_ = lean_unsigned_to_nat(1u);
v_a_564_ = lean_nat_sub(v_abs_562_, v_one_563_);
lean_dec(v_abs_562_);
v___x_565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_566_ = lean_nat_add(v_a_564_, v_one_563_);
lean_dec(v_a_564_);
v___x_567_ = l_Nat_reprFast(v___x_566_);
v___x_568_ = lean_string_append(v___x_565_, v___x_567_);
lean_dec_ref(v___x_567_);
v___y_536_ = v___x_568_;
goto v___jp_535_;
}
v___jp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_519_, 0, v___y_518_);
v___x_520_ = l_Lean_MessageData_ofFormat(v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___y_517_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_515_);
v___x_523_ = l_Lean_MessageData_ofExpr(v_a_513_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_481_, v___x_524_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec_ref(v___x_525_);
goto v___jp_492_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v___x_491_);
lean_del_object(v___x_485_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_intZero_547_; uint8_t v_isNeg_548_; 
v___x_537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_537_, 0, v___y_536_);
v___x_538_ = l_Lean_MessageData_ofFormat(v___x_537_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_534_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_515_);
v___x_541_ = l_Lean_MessageData_ofExpr(v_a_509_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_515_);
v___x_544_ = l_Lean_MessageData_ofExpr(v_a_511_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_515_);
v_intZero_547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v_isNeg_548_ = lean_int_dec_lt(v___x_487_, v_intZero_547_);
if (v_isNeg_548_ == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_nat_abs(v___x_487_);
lean_dec(v___x_487_);
v___x_550_ = l_Nat_reprFast(v_a_549_);
v___y_517_ = v___x_546_;
v___y_518_ = v___x_550_;
goto v___jp_516_;
}
else
{
lean_object* v_abs_551_; lean_object* v_one_552_; lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_abs_551_ = lean_nat_abs(v___x_487_);
lean_dec(v___x_487_);
v_one_552_ = lean_unsigned_to_nat(1u);
v_a_553_ = lean_nat_sub(v_abs_551_, v_one_552_);
lean_dec(v_abs_551_);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_555_ = lean_nat_add(v_a_553_, v_one_552_);
lean_dec(v_a_553_);
v___x_556_ = l_Nat_reprFast(v___x_555_);
v___x_557_ = lean_string_append(v___x_554_, v___x_556_);
lean_dec_ref(v___x_556_);
v___y_517_ = v___x_546_;
v___y_518_ = v___x_557_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_511_);
lean_dec(v_a_509_);
lean_dec(v_a_507_);
lean_dec(v___x_491_);
lean_dec(v___x_487_);
lean_del_object(v___x_485_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec(v_fst_472_);
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
v_a_569_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_512_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_512_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_509_);
lean_dec(v_a_507_);
lean_dec(v___x_491_);
lean_dec(v___x_487_);
lean_del_object(v___x_485_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec(v_fst_472_);
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
v_a_577_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_510_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_510_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_507_);
lean_dec(v___x_491_);
lean_dec(v___x_487_);
lean_del_object(v___x_485_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec(v_fst_472_);
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
v_a_585_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_508_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_508_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v___x_491_);
lean_dec(v___x_487_);
lean_del_object(v___x_485_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec(v_fst_472_);
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
v_a_593_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_506_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_506_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
v___jp_492_:
{
lean_object* v___x_494_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_491_);
lean_ctor_set(v___x_478_, 0, v_snd_471_);
v___x_494_ = v___x_478_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_snd_471_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_491_);
v___x_494_ = v_reuseFailAlloc_504_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_494_);
lean_ctor_set(v___x_474_, 0, v_fst_476_);
v___x_496_ = v___x_474_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fst_476_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_503_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_496_);
v___x_498_ = v___x_468_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_498_);
v___x_500_ = v___x_485_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
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
lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec(v_a_462_);
lean_dec(v_p_448_);
v___x_607_ = lean_box(0);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_607_);
v___x_609_ = v___x_464_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_p_448_);
v_a_612_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_461_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_461_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec(v_a_622_);
lean_dec(v_a_621_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object* v_cls_634_, lean_object* v_msg_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_634_, v_msg_635_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object* v_cls_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(v_cls_649_, v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec(v___y_652_);
lean_dec(v___y_651_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_p_677_; lean_object* v___x_678_; 
v_p_677_ = lean_ctor_get(v_c_664_, 0);
v___x_678_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_677_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v___x_678_);
v___x_680_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v_ofNatZero_682_; lean_object* v___x_683_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v_ofNatZero_682_ = lean_ctor_get(v_a_681_, 18);
lean_inc_ref(v_ofNatZero_682_);
lean_dec(v_a_681_);
v___x_683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(v_a_679_, v_ofNatZero_682_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_mkNot(v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
return v___x_683_;
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v_a_679_);
v_a_693_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_680_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_680_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v_c_701_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_719_, lean_object* v_x_720_, lean_object* v_c_u2081_721_, lean_object* v_b_722_, lean_object* v_c_u2082_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v_cls_790_; lean_object* v___x_791_; lean_object* v_a_792_; uint8_t v___x_793_; 
v_cls_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0));
v___x_791_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_790_, v_a_733_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_unbox(v_a_792_);
lean_dec(v_a_792_);
if (v___x_793_ == 0)
{
v___y_737_ = v_a_724_;
v___y_738_ = v_a_725_;
v___y_739_ = v_a_726_;
v___y_740_ = v_a_727_;
v___y_741_ = v_a_728_;
v___y_742_ = v_a_729_;
v___y_743_ = v_a_730_;
v___y_744_ = v_a_731_;
v___y_745_ = v_a_732_;
v___y_746_ = v_a_733_;
v___y_747_ = v_a_734_;
goto v___jp_736_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_720_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_u2081_721_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Lean_MessageData_ofExpr(v_a_795_);
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_MessageData_ofExpr(v_a_797_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_801_);
v___x_806_ = l_Lean_MessageData_ofExpr(v_a_799_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_790_, v___x_807_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_dec_ref(v___x_808_);
v___y_737_ = v_a_724_;
v___y_738_ = v_a_725_;
v___y_739_ = v_a_726_;
v___y_740_ = v_a_727_;
v___y_741_ = v_a_728_;
v___y_742_ = v_a_729_;
v___y_743_ = v_a_730_;
v___y_744_ = v_a_731_;
v___y_745_ = v_a_732_;
v___y_746_ = v_a_733_;
v___y_747_ = v_a_734_;
goto v___jp_736_;
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_a_797_);
lean_dec(v_a_795_);
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v_a_817_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_798_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_798_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_795_);
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v_a_825_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_796_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_796_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v_a_833_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_794_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_794_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
v___jp_736_:
{
lean_object* v_p_748_; lean_object* v_p_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_p_748_ = lean_ctor_get(v_c_u2081_721_, 0);
v_p_749_ = lean_ctor_get(v_c_u2082_723_, 0);
v___x_750_ = lean_int_emod(v_b_722_, v_a_719_);
v___x_751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_752_ = lean_int_dec_eq(v___x_750_, v___x_751_);
lean_dec(v___x_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_773_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_773_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_773_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_773_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
uint8_t v___x_758_; 
v___x_758_ = lean_unbox(v_a_754_);
lean_dec(v_a_754_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v___x_759_ = lean_box(0);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_759_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
lean_inc(v_p_748_);
v___x_763_ = l_Lean_Grind_Linarith_Poly_mul(v_p_748_, v_b_722_);
v___x_764_ = lean_int_neg(v_a_719_);
lean_inc(v_p_749_);
v___x_765_ = l_Lean_Grind_Linarith_Poly_mul(v_p_749_, v___x_764_);
v___x_766_ = l_Lean_Grind_Linarith_Poly_combine(v___x_763_, v___x_765_);
v___x_767_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v_b_722_);
lean_ctor_set(v___x_767_, 2, v_c_u2081_721_);
lean_ctor_set(v___x_767_, 3, v_c_u2082_723_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_769_);
v___x_771_ = v___x_756_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_c_u2082_723_);
lean_dec(v_b_722_);
lean_dec_ref(v_c_u2081_721_);
v_a_774_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_753_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_753_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_782_ = lean_int_neg(v_b_722_);
lean_dec(v_b_722_);
v___x_783_ = lean_int_ediv(v___x_782_, v_a_719_);
lean_dec(v___x_782_);
lean_inc(v_p_748_);
v___x_784_ = l_Lean_Grind_Linarith_Poly_mul(v_p_748_, v___x_783_);
lean_inc(v_p_749_);
v___x_785_ = l_Lean_Grind_Linarith_Poly_combine(v___x_784_, v_p_749_);
v___x_786_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v_c_u2081_721_);
lean_ctor_set(v___x_786_, 2, v_c_u2082_723_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_841_ = _args[0];
lean_object* v_x_842_ = _args[1];
lean_object* v_c_u2081_843_ = _args[2];
lean_object* v_b_844_ = _args[3];
lean_object* v_c_u2082_845_ = _args[4];
lean_object* v_a_846_ = _args[5];
lean_object* v_a_847_ = _args[6];
lean_object* v_a_848_ = _args[7];
lean_object* v_a_849_ = _args[8];
lean_object* v_a_850_ = _args[9];
lean_object* v_a_851_ = _args[10];
lean_object* v_a_852_ = _args[11];
lean_object* v_a_853_ = _args[12];
lean_object* v_a_854_ = _args[13];
lean_object* v_a_855_ = _args[14];
lean_object* v_a_856_ = _args[15];
lean_object* v_a_857_ = _args[16];
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_841_, v_x_842_, v_c_u2081_843_, v_b_844_, v_c_u2082_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_x_842_);
lean_dec(v_a_841_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_859_, lean_object* v_b_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_859_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_893_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_893_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_893_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_893_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
if (lean_obj_tag(v_a_865_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_870_; 
lean_del_object(v___x_867_);
v_val_869_ = lean_ctor_get(v_a_865_, 0);
v___x_870_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_888_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_888_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_888_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_875_; uint8_t v___x_876_; 
v_val_875_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_875_);
lean_dec_ref(v_a_871_);
v___x_876_ = lean_nat_dec_eq(v_val_869_, v_val_875_);
lean_dec(v_val_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec_ref(v_a_865_);
v___x_877_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_882_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_a_865_);
v___x_882_ = v___x_873_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_865_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v_a_871_);
lean_dec_ref(v_a_865_);
v___x_884_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_884_);
v___x_886_ = v___x_873_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_dec_ref(v_a_865_);
return v___x_870_;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_a_865_);
v___x_889_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_889_);
v___x_891_ = v___x_867_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_894_, lean_object* v_b_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_894_, v_b_895_, v_a_896_, v_a_897_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_b_895_);
lean_dec_ref(v_a_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_900_, lean_object* v_b_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_900_, v_b_901_, v_a_902_, v_a_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_914_, lean_object* v_b_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_914_, v_b_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_b_915_);
lean_dec_ref(v_a_914_);
return v_res_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_929_ = lean_int_neg(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_930_, lean_object* v_b_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_944_ = 0;
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_box(v___x_944_);
lean_inc_ref(v_a_930_);
v___x_947_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_947_, 0, v_a_930_);
lean_closure_set(v___x_947_, 1, v___x_946_);
lean_closure_set(v___x_947_, 2, v___x_945_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
v___x_948_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_947_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_1100_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_1100_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_1100_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
if (lean_obj_tag(v_a_949_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_951_);
v_val_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_a_949_);
v___x_954_ = lean_box(v___x_944_);
lean_inc_ref(v_b_931_);
v___x_955_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_955_, 0, v_b_931_);
lean_closure_set(v___x_955_, 1, v___x_954_);
lean_closure_set(v___x_955_, 2, v___x_945_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
v___x_956_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_955_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1087_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_1087_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1087_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
if (lean_obj_tag(v_a_957_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_962_; 
lean_del_object(v___x_959_);
v_val_961_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_val_961_);
lean_dec_ref(v_a_957_);
v___x_962_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_930_, v_a_933_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_931_, v_a_933_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___y_967_; uint8_t v___x_1066_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
v___x_1066_ = lean_nat_dec_le(v_a_963_, v_a_965_);
if (v___x_1066_ == 0)
{
lean_dec(v_a_965_);
v___y_967_ = v_a_963_;
goto v___jp_966_;
}
else
{
lean_dec(v_a_963_);
v___y_967_ = v_a_965_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_inc(v_val_961_);
lean_inc(v_val_953_);
v___x_968_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_968_, 0, v_val_953_);
lean_ctor_set(v___x_968_, 1, v_val_961_);
v___x_969_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_970_, 0, v_a_930_);
lean_ctor_set(v___x_970_, 1, v_b_931_);
lean_ctor_set(v___x_970_, 2, v_val_953_);
lean_ctor_set(v___x_970_, 3, v_val_961_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
v___x_972_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_971_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_p_974_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v_p_974_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v___y_967_);
lean_inc_ref(v_p_974_);
v___x_975_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_974_, v___y_967_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v_a_932_);
lean_inc(v___y_967_);
v___x_977_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_976_, v___x_944_, v___y_967_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1041_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1041_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1041_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
if (lean_obj_tag(v_a_978_) == 1)
{
lean_object* v_val_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_val_982_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_val_982_);
lean_dec_ref(v_a_978_);
lean_inc(v_val_982_);
v___x_983_ = l_Lean_Grind_Linarith_Expr_norm(v_val_982_);
v___x_984_ = lean_box(0);
v___x_985_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_del_object(v___x_980_);
lean_inc(v_a_973_);
v___x_986_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_986_, 0, v_a_973_);
lean_ctor_set(v___x_986_, 1, v_val_982_);
lean_inc(v___x_983_);
v___x_987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_987_, 0, v___x_983_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*2, v___x_944_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v_a_932_);
v___x_988_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_987_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1031_; 
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_988_, 0);
lean_dec(v_unused_1032_);
v___x_990_ = v___x_988_;
v_isShared_991_ = v_isSharedCheck_1031_;
goto v_resetjp_989_;
}
else
{
lean_dec(v___x_988_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1031_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_974_);
v___x_993_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_992_, v_p_974_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v_a_973_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_973_);
v___x_995_ = v_reuseFailAlloc_1030_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_inc_ref(v___x_993_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_993_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v___y_967_);
v___x_997_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_993_, v___y_967_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
lean_inc(v_a_942_);
lean_inc_ref(v_a_941_);
lean_inc(v_a_940_);
lean_inc_ref(v_a_939_);
lean_inc(v_a_938_);
lean_inc_ref(v_a_937_);
lean_inc(v_a_936_);
lean_inc_ref(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v_a_932_);
v___x_999_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_998_, v___x_944_, v___y_967_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1013_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
if (lean_obj_tag(v_a_1000_) == 1)
{
lean_object* v_val_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_1002_);
v_val_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v_a_1000_);
v___x_1005_ = l_Lean_Grind_Linarith_Poly_mul(v___x_983_, v___x_992_);
v___x_1006_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_996_);
lean_ctor_set(v___x_1006_, 1, v_val_1004_);
v___x_1007_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*2, v___x_944_);
v___x_1008_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1007_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
lean_dec(v_a_1000_);
lean_dec_ref(v___x_996_);
lean_dec(v___x_983_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v___x_1009_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1009_);
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v___x_996_);
lean_dec(v___x_983_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v_a_1014_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_999_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_999_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v___x_996_);
lean_dec(v___x_983_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v_a_1022_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_997_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_997_);
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
}
}
else
{
lean_dec(v___x_983_);
lean_dec(v_a_973_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
return v___x_988_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec(v___x_983_);
lean_dec(v_val_982_);
lean_dec(v_a_973_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v___x_1033_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_1033_);
v___x_1035_ = v___x_980_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_dec(v_a_978_);
lean_dec(v_a_973_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v___x_1037_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_1037_);
v___x_1039_ = v___x_980_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_973_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v_a_1042_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_977_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_977_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_973_);
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v_a_1050_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_975_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_975_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___y_967_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
v_a_1058_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_972_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_972_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_963_);
lean_dec(v_val_961_);
lean_dec(v_val_953_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v_a_1067_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_964_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_964_);
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
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_val_961_);
lean_dec(v_val_953_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v_a_1075_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_962_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_962_);
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
else
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_dec(v_a_957_);
lean_dec(v_val_953_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v___x_1083_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_1083_);
v___x_1085_ = v___x_959_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_val_953_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v_a_1088_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_956_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_956_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
lean_dec(v_a_949_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v___x_1096_ = lean_box(0);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_1096_);
v___x_1098_ = v___x_951_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_a_930_);
v_a_1101_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_948_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_948_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1109_, lean_object* v_b_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1109_, v_b_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1124_, lean_object* v_b_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1124_, v_a_1127_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = 0;
lean_inc(v_a_1136_);
lean_inc_ref(v_a_1135_);
lean_inc(v_a_1134_);
lean_inc_ref(v_a_1133_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_a_1124_);
v___x_1141_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1124_, v___x_1140_, v_a_1139_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1196_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1196_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1196_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
if (lean_obj_tag(v_a_1142_) == 1)
{
lean_object* v_val_1146_; lean_object* v___x_1147_; 
lean_del_object(v___x_1144_);
v_val_1146_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_val_1146_);
lean_dec_ref(v_a_1142_);
v___x_1147_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1125_, v_a_1127_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1147_);
lean_inc(v_a_1136_);
lean_inc_ref(v_a_1135_);
lean_inc(v_a_1134_);
lean_inc_ref(v_a_1133_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_b_1125_);
v___x_1149_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1125_, v___x_1140_, v_a_1148_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1175_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1175_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1175_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
if (lean_obj_tag(v_a_1150_) == 1)
{
lean_object* v_val_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_val_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_val_1154_);
lean_dec_ref(v_a_1150_);
lean_inc(v_val_1154_);
lean_inc(v_val_1146_);
v___x_1155_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_val_1146_);
lean_ctor_set(v___x_1155_, 1, v_val_1154_);
v___x_1156_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1152_);
lean_inc(v_val_1154_);
lean_inc(v_val_1146_);
lean_inc_ref(v_b_1125_);
lean_inc_ref(v_a_1124_);
v___x_1159_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1124_);
lean_ctor_set(v___x_1159_, 1, v_b_1125_);
lean_ctor_set(v___x_1159_, 2, v_val_1146_);
lean_ctor_set(v___x_1159_, 3, v_val_1154_);
lean_inc(v___x_1156_);
v___x_1160_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1160_, 0, v___x_1156_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*2, v___x_1140_);
lean_inc(v_a_1136_);
lean_inc_ref(v_a_1135_);
lean_inc(v_a_1134_);
lean_inc_ref(v_a_1133_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
v___x_1161_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1160_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v___x_1161_);
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1163_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1156_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1125_);
lean_ctor_set(v___x_1164_, 1, v_a_1124_);
lean_ctor_set(v___x_1164_, 2, v_val_1154_);
lean_ctor_set(v___x_1164_, 3, v_val_1146_);
v___x_1165_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*2, v___x_1140_);
v___x_1166_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1165_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1166_;
}
else
{
lean_dec(v___x_1156_);
lean_dec(v_val_1154_);
lean_dec(v_val_1146_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_dec(v___x_1156_);
lean_dec(v_val_1154_);
lean_dec(v_val_1146_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v___x_1167_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1167_);
v___x_1169_ = v___x_1152_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec(v_a_1150_);
lean_dec(v_val_1146_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v___x_1171_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1171_);
v___x_1173_ = v___x_1152_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
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
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_val_1146_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v_a_1176_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1149_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1149_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_val_1146_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v_a_1184_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1147_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1147_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec(v_a_1142_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v___x_1192_ = lean_box(0);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1192_);
v___x_1194_ = v___x_1144_;
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
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v_a_1197_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1141_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1141_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_b_1125_);
lean_dec_ref(v_a_1124_);
v_a_1205_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1138_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1138_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1213_, lean_object* v_b_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1213_, v_b_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
return v_res_1227_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v___f_1243_; lean_object* v___x_3554__overap_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1243_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1243_, 0, v___x_1242_);
v___x_3554__overap_1244_ = lean_panic_fn(v___f_1243_, v_msg_1229_);
v___x_1245_ = lean_apply_12(v___x_3554__overap_1244_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, lean_box(0));
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_nat_to_int(v_a_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1266_ = lean_unsigned_to_nat(42u);
v___x_1267_ = lean_unsigned_to_nat(87u);
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1270_ = l_mkPanicMessageWithDecl(v___x_1269_, v___x_1268_, v___x_1267_, v___x_1266_, v___x_1265_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v_c_1287_; lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v_c_1295_; lean_object* v_p_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; uint8_t v___x_1332_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1332_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1332_ == 0)
{
lean_object* v_p_1333_; 
v_p_1333_ = lean_ctor_get(v_c_1271_, 0);
lean_inc(v_p_1333_);
v_c_1295_ = v_c_1271_;
v_p_1296_ = v_p_1333_;
v___y_1297_ = v_a_1272_;
v___y_1298_ = v_a_1273_;
v___y_1299_ = v_a_1274_;
v___y_1300_ = v_a_1275_;
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
goto v___jp_1294_;
}
else
{
lean_object* v_p_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_p_1334_ = lean_ctor_get(v_c_1271_, 0);
v___x_1335_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1334_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc(v___x_1335_);
v___x_1338_ = lean_nat_to_int(v___x_1335_);
lean_inc(v_p_1334_);
v___x_1339_ = l_Lean_Grind_Linarith_Poly_div(v_p_1334_, v___x_1338_);
lean_dec(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1335_);
lean_ctor_set(v___x_1340_, 1, v_c_1271_);
lean_inc(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v_c_1295_ = v___x_1341_;
v_p_1296_ = v___x_1339_;
v___y_1297_ = v_a_1272_;
v___y_1298_ = v_a_1273_;
v___y_1299_ = v_a_1274_;
v___y_1300_ = v_a_1275_;
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
goto v___jp_1294_;
}
else
{
lean_inc(v_p_1334_);
lean_dec(v___x_1335_);
v_c_1295_ = v_c_1271_;
v_p_1296_ = v_p_1334_;
v___y_1297_ = v_a_1272_;
v___y_1298_ = v_a_1273_;
v___y_1299_ = v_a_1274_;
v___y_1300_ = v_a_1275_;
v___y_1301_ = v_a_1276_;
v___y_1302_ = v_a_1277_;
v___y_1303_ = v_a_1278_;
v___y_1304_ = v_a_1279_;
v___y_1305_ = v_a_1280_;
v___y_1306_ = v_a_1281_;
v___y_1307_ = v_a_1282_;
goto v___jp_1294_;
}
}
v___jp_1294_:
{
lean_object* v___x_1308_; 
lean_inc(v_p_1296_);
v___x_1308_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1296_);
if (lean_obj_tag(v___x_1308_) == 1)
{
lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v___y_1297_);
v_val_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1329_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1329_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
v_fst_1313_ = lean_ctor_get(v_val_1309_, 0);
v_snd_1314_ = lean_ctor_get(v_val_1309_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_val_1309_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1316_ = v_val_1309_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_snd_1314_);
lean_inc(v_fst_1313_);
lean_dec(v_val_1309_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1319_ = lean_int_dec_lt(v_fst_1313_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_del_object(v___x_1316_);
lean_del_object(v___x_1311_);
lean_dec(v_p_1296_);
v___y_1285_ = v_snd_1314_;
v___y_1286_ = v_fst_1313_;
v_c_1287_ = v_c_1295_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1321_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1296_, v___x_1320_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 3);
lean_ctor_set(v___x_1311_, 0, v_c_1295_);
v___x_1323_ = v___x_1311_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_c_1295_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___x_1323_);
lean_ctor_set(v___x_1316_, 0, v___x_1321_);
v___x_1325_ = v___x_1316_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v___y_1285_ = v_snd_1314_;
v___y_1286_ = v_fst_1313_;
v_c_1287_ = v___x_1325_;
goto v___jp_1284_;
}
}
}
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v___x_1308_);
lean_dec(v_p_1296_);
lean_dec_ref(v_c_1295_);
v___x_1330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1331_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1330_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_c_1271_);
v_a_1342_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1292_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1292_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
v___jp_1284_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = lean_nat_abs(v___y_1286_);
lean_dec(v___y_1286_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1285_);
lean_ctor_set(v___x_1289_, 1, v_c_1287_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v_res_1363_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = l_Lean_maxRecDepthErrorMessage;
v___x_1370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1372_ = l_Lean_MessageData_ofFormat(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1374_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_ref_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1385_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_ref_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1399_, v_ref_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec(v___y_1401_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_fileName_1427_; lean_object* v_fileMap_1428_; lean_object* v_options_1429_; lean_object* v_currRecDepth_1430_; lean_object* v_maxRecDepth_1431_; lean_object* v_ref_1432_; lean_object* v_currNamespace_1433_; lean_object* v_openDecls_1434_; lean_object* v_initHeartbeats_1435_; lean_object* v_maxHeartbeats_1436_; lean_object* v_quotContext_1437_; lean_object* v_currMacroScope_1438_; uint8_t v_diag_1439_; lean_object* v_cancelTk_x3f_1440_; uint8_t v_suppressElabErrors_1441_; lean_object* v_inheritedTraceOptions_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1562_; 
v_fileName_1427_ = lean_ctor_get(v_a_1424_, 0);
v_fileMap_1428_ = lean_ctor_get(v_a_1424_, 1);
v_options_1429_ = lean_ctor_get(v_a_1424_, 2);
v_currRecDepth_1430_ = lean_ctor_get(v_a_1424_, 3);
v_maxRecDepth_1431_ = lean_ctor_get(v_a_1424_, 4);
v_ref_1432_ = lean_ctor_get(v_a_1424_, 5);
v_currNamespace_1433_ = lean_ctor_get(v_a_1424_, 6);
v_openDecls_1434_ = lean_ctor_get(v_a_1424_, 7);
v_initHeartbeats_1435_ = lean_ctor_get(v_a_1424_, 8);
v_maxHeartbeats_1436_ = lean_ctor_get(v_a_1424_, 9);
v_quotContext_1437_ = lean_ctor_get(v_a_1424_, 10);
v_currMacroScope_1438_ = lean_ctor_get(v_a_1424_, 11);
v_diag_1439_ = lean_ctor_get_uint8(v_a_1424_, sizeof(void*)*14);
v_cancelTk_x3f_1440_ = lean_ctor_get(v_a_1424_, 12);
v_suppressElabErrors_1441_ = lean_ctor_get_uint8(v_a_1424_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1442_ = lean_ctor_get(v_a_1424_, 13);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1444_ = v_a_1424_;
v_isShared_1445_ = v_isSharedCheck_1562_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_inheritedTraceOptions_1442_);
lean_inc(v_cancelTk_x3f_1440_);
lean_inc(v_currMacroScope_1438_);
lean_inc(v_quotContext_1437_);
lean_inc(v_maxHeartbeats_1436_);
lean_inc(v_initHeartbeats_1435_);
lean_inc(v_openDecls_1434_);
lean_inc(v_currNamespace_1433_);
lean_inc(v_ref_1432_);
lean_inc(v_maxRecDepth_1431_);
lean_inc(v_currRecDepth_1430_);
lean_inc(v_options_1429_);
lean_inc(v_fileMap_1428_);
lean_inc(v_fileName_1427_);
lean_dec(v_a_1424_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1562_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_eq(v_currRecDepth_1430_, v_maxRecDepth_1431_);
if (v___x_1446_ == 0)
{
lean_object* v_p_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v_p_1447_ = lean_ctor_get(v_c_1414_, 0);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_currRecDepth_1430_, v___x_1448_);
lean_dec(v_currRecDepth_1430_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 3, v___x_1449_);
v___x_1451_ = v___x_1444_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_fileName_1427_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_fileMap_1428_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_options_1429_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_maxRecDepth_1431_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v_ref_1432_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_currNamespace_1433_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v_openDecls_1434_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v_initHeartbeats_1435_);
lean_ctor_set(v_reuseFailAlloc_1560_, 9, v_maxHeartbeats_1436_);
lean_ctor_set(v_reuseFailAlloc_1560_, 10, v_quotContext_1437_);
lean_ctor_set(v_reuseFailAlloc_1560_, 11, v_currMacroScope_1438_);
lean_ctor_set(v_reuseFailAlloc_1560_, 12, v_cancelTk_x3f_1440_);
lean_ctor_set(v_reuseFailAlloc_1560_, 13, v_inheritedTraceOptions_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*14, v_diag_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*14 + 1, v_suppressElabErrors_1441_);
v___x_1451_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
lean_inc(v_p_1447_);
v___x_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1447_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v___x_1451_, v_a_1425_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1551_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1551_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1551_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
if (lean_obj_tag(v_a_1453_) == 1)
{
lean_object* v_val_1457_; lean_object* v_snd_1458_; lean_object* v_fst_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1547_; 
lean_del_object(v___x_1455_);
v_val_1457_ = lean_ctor_get(v_a_1453_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v_a_1453_);
v_snd_1458_ = lean_ctor_get(v_val_1457_, 1);
v_fst_1459_ = lean_ctor_get(v_val_1457_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_val_1457_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1461_ = v_val_1457_;
v_isShared_1462_ = v_isSharedCheck_1547_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1458_);
lean_inc(v_fst_1459_);
lean_dec(v_val_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1547_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_fst_1463_; lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1546_; 
v_fst_1463_ = lean_ctor_get(v_snd_1458_, 0);
v_snd_1464_ = lean_ctor_get(v_snd_1458_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_snd_1458_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1466_ = v_snd_1458_;
v_isShared_1467_ = v_isSharedCheck_1546_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_inc(v_fst_1463_);
lean_dec(v_snd_1458_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1546_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1486_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_1485_, v___x_1451_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; uint8_t v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = lean_unbox(v_a_1487_);
lean_dec(v_a_1487_);
if (v___x_1488_ == 0)
{
lean_del_object(v___x_1461_);
v___y_1469_ = v_a_1415_;
v___y_1470_ = v_a_1416_;
v___y_1471_ = v_a_1417_;
v___y_1472_ = v_a_1418_;
v___y_1473_ = v_a_1419_;
v___y_1474_ = v_a_1420_;
v___y_1475_ = v_a_1421_;
v___y_1476_ = v_a_1422_;
v___y_1477_ = v_a_1423_;
v___y_1478_ = v___x_1451_;
v___y_1479_ = v_a_1425_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1459_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v___x_1451_, v_a_1425_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v___x_1451_, v_a_1425_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_fst_1463_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v___x_1451_, v_a_1425_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_MessageData_ofExpr(v_a_1490_);
v___x_1496_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 7);
lean_ctor_set(v___x_1461_, 1, v___x_1496_);
lean_ctor_set(v___x_1461_, 0, v___x_1495_);
v___x_1498_ = v___x_1461_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1499_ = l_Lean_MessageData_ofExpr(v_a_1492_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___x_1496_);
v___x_1502_ = l_Lean_MessageData_ofExpr(v_a_1494_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_1485_, v___x_1503_, v_a_1422_, v_a_1423_, v___x_1451_, v_a_1425_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_dec_ref(v___x_1504_);
v___y_1469_ = v_a_1415_;
v___y_1470_ = v_a_1416_;
v___y_1471_ = v_a_1417_;
v___y_1472_ = v_a_1418_;
v___y_1473_ = v_a_1419_;
v___y_1474_ = v_a_1420_;
v___y_1475_ = v_a_1421_;
v___y_1476_ = v_a_1422_;
v___y_1477_ = v_a_1423_;
v___y_1478_ = v___x_1451_;
v___y_1479_ = v_a_1425_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1463_);
lean_dec(v_fst_1459_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1492_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1463_);
lean_del_object(v___x_1461_);
lean_dec(v_fst_1459_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1514_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1493_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1493_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_a_1490_);
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1463_);
lean_del_object(v___x_1461_);
lean_dec(v_fst_1459_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1522_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1491_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1491_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1463_);
lean_del_object(v___x_1461_);
lean_dec(v_fst_1459_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1530_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1489_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1489_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1463_);
lean_del_object(v___x_1461_);
lean_dec(v_fst_1459_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1538_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1486_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1486_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
v___jp_1468_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1480_, 0, v_fst_1459_);
lean_ctor_set(v___x_1480_, 1, v_fst_1463_);
lean_ctor_set(v___x_1480_, 2, v_c_1414_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1480_);
lean_ctor_set(v___x_1466_, 0, v_snd_1464_);
v___x_1482_ = v___x_1466_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_snd_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
v_c_1414_ = v___x_1482_;
v_a_1415_ = v___y_1469_;
v_a_1416_ = v___y_1470_;
v_a_1417_ = v___y_1471_;
v_a_1418_ = v___y_1472_;
v_a_1419_ = v___y_1473_;
v_a_1420_ = v___y_1474_;
v_a_1421_ = v___y_1475_;
v_a_1422_ = v___y_1476_;
v_a_1423_ = v___y_1477_;
v_a_1424_ = v___y_1478_;
v_a_1425_ = v___y_1479_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1549_; 
lean_dec(v_a_1453_);
lean_dec_ref(v___x_1451_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_c_1414_);
v___x_1549_ = v___x_1455_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_c_1414_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_c_1414_);
v_a_1552_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1452_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1452_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
lean_object* v___x_1561_; 
lean_del_object(v___x_1444_);
lean_dec_ref(v_inheritedTraceOptions_1442_);
lean_dec(v_cancelTk_x3f_1440_);
lean_dec(v_currMacroScope_1438_);
lean_dec(v_quotContext_1437_);
lean_dec(v_maxHeartbeats_1436_);
lean_dec(v_initHeartbeats_1435_);
lean_dec(v_openDecls_1434_);
lean_dec(v_currNamespace_1433_);
lean_dec(v_maxRecDepth_1431_);
lean_dec(v_currRecDepth_1430_);
lean_dec_ref(v_options_1429_);
lean_dec_ref(v_fileMap_1428_);
lean_dec_ref(v_fileName_1427_);
lean_dec_ref(v_c_1414_);
v___x_1561_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1432_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec(v_a_1564_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_ref_1583_; lean_object* v___x_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1593_; 
v_ref_1583_ = lean_ctor_get(v___y_1580_, 5);
v___x_1584_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(v_msg_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_inc(v_ref_1583_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_ref_1583_);
lean_ctor_set(v___x_1589_, 1, v_a_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1628_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_leFn_x3f_1621_; 
v_leFn_x3f_1621_ = lean_ctor_get(v_a_1617_, 20);
lean_inc(v_leFn_x3f_1621_);
lean_dec(v_a_1617_);
if (lean_obj_tag(v_leFn_x3f_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; 
v_val_1622_ = lean_ctor_get(v_leFn_x3f_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref(v_leFn_x3f_1621_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_val_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_leFn_x3f_1621_);
lean_del_object(v___x_1619_);
v___x_1626_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1627_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1626_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1627_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1616_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1616_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v___y_1637_);
return v_res_1649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_ltFn_x3f_1670_; 
v_ltFn_x3f_1670_ = lean_ctor_get(v_a_1666_, 21);
lean_inc(v_ltFn_x3f_1670_);
lean_dec(v_a_1666_);
if (lean_obj_tag(v_ltFn_x3f_1670_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; 
v_val_1671_ = lean_ctor_get(v_ltFn_x3f_1670_, 0);
lean_inc(v_val_1671_);
lean_dec_ref(v_ltFn_x3f_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v_val_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_val_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_ltFn_x3f_1670_);
lean_del_object(v___x_1668_);
v___x_1675_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1676_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1675_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1665_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1665_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___y_1686_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1699_, uint8_t v_strict_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
if (v_strict_1700_ == 0)
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1699_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
v___x_1717_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_ofNatZero_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v_ofNatZero_1722_ = lean_ctor_get(v_a_1718_, 18);
lean_inc_ref(v_ofNatZero_1722_);
lean_dec(v_a_1718_);
v___x_1723_ = l_Lean_mkAppB(v_a_1714_, v_a_1716_, v_ofNatZero_1722_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_a_1716_);
lean_dec(v_a_1714_);
v_a_1728_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1717_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1717_);
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
lean_dec(v_a_1714_);
return v___x_1715_;
}
}
else
{
return v___x_1713_;
}
}
else
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1699_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1750_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_ofNatZero_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v_ofNatZero_1745_ = lean_ctor_get(v_a_1741_, 18);
lean_inc_ref(v_ofNatZero_1745_);
lean_dec(v_a_1741_);
v___x_1746_ = l_Lean_mkAppB(v_a_1737_, v_a_1739_, v_ofNatZero_1745_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1746_);
v___x_1748_ = v___x_1743_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_a_1739_);
lean_dec(v_a_1737_);
v_a_1751_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1740_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1740_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_dec(v_a_1737_);
return v___x_1738_;
}
}
else
{
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1759_, lean_object* v_strict_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_strict_boxed_1773_; lean_object* v_res_1774_; 
v_strict_boxed_1773_ = lean_unbox(v_strict_1760_);
v_res_1774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1759_, v_strict_boxed_1773_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v_p_1759_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_p_1788_; uint8_t v_strict_1789_; lean_object* v___x_1790_; 
v_p_1788_ = lean_ctor_get(v_c_1775_, 0);
v_strict_1789_ = lean_ctor_get_uint8(v_c_1775_, sizeof(void*)*2);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1788_, v_strict_1789_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v_c_1791_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1805_, lean_object* v_x_1806_, lean_object* v_c_u2081_1807_, lean_object* v_b_1808_, lean_object* v_c_u2082_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_cls_1822_; lean_object* v___x_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1890_; 
v_cls_1822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0));
v___x_1823_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_1822_, v_a_1819_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1890_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1890_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_p_1828_; lean_object* v_p_1829_; uint8_t v_strict_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_p_1835_; uint8_t v___x_1842_; 
v_p_1828_ = lean_ctor_get(v_c_u2081_1807_, 0);
v_p_1829_ = lean_ctor_get(v_c_u2082_1809_, 0);
v_strict_1830_ = lean_ctor_get_uint8(v_c_u2082_1809_, sizeof(void*)*2);
v___x_1831_ = lean_nat_to_int(v_a_1805_);
lean_inc(v_p_1829_);
v___x_1832_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1829_, v___x_1831_);
lean_dec(v___x_1831_);
v___x_1833_ = lean_int_neg(v_b_1808_);
lean_inc(v_p_1828_);
v___x_1834_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1828_, v___x_1833_);
lean_dec(v___x_1833_);
v_p_1835_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1832_, v___x_1834_);
v___x_1842_ = lean_unbox(v_a_1824_);
lean_dec(v_a_1824_);
if (v___x_1842_ == 0)
{
goto v___jp_1836_;
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1806_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_u2081_1807_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = l_Lean_MessageData_ofExpr(v_a_1844_);
v___x_1850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_MessageData_ofExpr(v_a_1846_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1850_);
v___x_1855_ = l_Lean_MessageData_ofExpr(v_a_1848_);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_1822_, v___x_1856_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_dec_ref(v___x_1857_);
goto v___jp_1836_;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_p_1835_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_c_u2082_1809_);
lean_dec_ref(v_c_u2081_1807_);
lean_dec(v_x_1806_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1846_);
lean_dec(v_a_1844_);
lean_dec(v_p_1835_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_c_u2082_1809_);
lean_dec_ref(v_c_u2081_1807_);
lean_dec(v_x_1806_);
v_a_1866_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1847_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1847_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1844_);
lean_dec(v_p_1835_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_c_u2082_1809_);
lean_dec_ref(v_c_u2081_1807_);
lean_dec(v_x_1806_);
v_a_1874_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1845_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1845_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_p_1835_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_c_u2082_1809_);
lean_dec_ref(v_c_u2081_1807_);
lean_dec(v_x_1806_);
v_a_1882_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1843_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1843_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1836_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1837_, 0, v_x_1806_);
lean_ctor_set(v___x_1837_, 1, v_c_u2081_1807_);
lean_ctor_set(v___x_1837_, 2, v_c_u2082_1809_);
v___x_1838_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1838_, 0, v_p_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*2, v_strict_1830_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1838_);
v___x_1840_ = v___x_1826_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1891_ = _args[0];
lean_object* v_x_1892_ = _args[1];
lean_object* v_c_u2081_1893_ = _args[2];
lean_object* v_b_1894_ = _args[3];
lean_object* v_c_u2082_1895_ = _args[4];
lean_object* v_a_1896_ = _args[5];
lean_object* v_a_1897_ = _args[6];
lean_object* v_a_1898_ = _args[7];
lean_object* v_a_1899_ = _args[8];
lean_object* v_a_1900_ = _args[9];
lean_object* v_a_1901_ = _args[10];
lean_object* v_a_1902_ = _args[11];
lean_object* v_a_1903_ = _args[12];
lean_object* v_a_1904_ = _args[13];
lean_object* v_a_1905_ = _args[14];
lean_object* v_a_1906_ = _args[15];
lean_object* v_a_1907_ = _args[16];
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1891_, v_x_1892_, v_c_u2081_1893_, v_b_1894_, v_c_u2082_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec(v_b_1894_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1909_, lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1910_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1924_, v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1947_, lean_object* v_x_1948_, lean_object* v_c_u2081_1949_, lean_object* v_as_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_c_u2081_1949_);
lean_dec(v_x_1948_);
lean_dec(v_a_1947_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1953_);
return v___x_1967_;
}
else
{
lean_object* v_a_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_b_1953_);
v_a_1968_ = lean_array_uget_borrowed(v_as_1950_, v_i_1952_);
v_fst_1969_ = lean_ctor_get(v_a_1968_, 0);
v_snd_1970_ = lean_ctor_get(v_a_1968_, 1);
lean_inc(v_snd_1970_);
lean_inc_ref(v_c_u2081_1949_);
lean_inc(v_x_1948_);
lean_inc(v_a_1947_);
v___x_1971_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1947_, v_x_1948_, v_c_u2081_1949_, v_fst_1969_, v_snd_1970_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc(v___y_1954_);
v___x_1973_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1972_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref(v___x_1973_);
v___x_1974_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1988_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; size_t v___x_1981_; size_t v___x_1982_; 
lean_del_object(v___x_1977_);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1981_ = ((size_t)1ULL);
v___x_1982_ = lean_usize_add(v_i_1952_, v___x_1981_);
v_i_1952_ = v___x_1982_;
v_b_1953_ = v___x_1980_;
goto _start;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_c_u2081_1949_);
lean_dec(v_x_1948_);
lean_dec(v_a_1947_);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1984_);
v___x_1986_ = v___x_1977_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_c_u2081_1949_);
lean_dec(v_x_1948_);
lean_dec(v_a_1947_);
v_a_1989_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1974_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1974_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_c_u2081_1949_);
lean_dec(v_x_1948_);
lean_dec(v_a_1947_);
v_a_1997_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1973_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1973_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v_c_u2081_1949_);
lean_dec(v_x_1948_);
lean_dec(v_a_1947_);
v_a_2005_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1971_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1971_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_2013_ = _args[0];
lean_object* v_x_2014_ = _args[1];
lean_object* v_c_u2081_2015_ = _args[2];
lean_object* v_as_2016_ = _args[3];
lean_object* v_sz_2017_ = _args[4];
lean_object* v_i_2018_ = _args[5];
lean_object* v_b_2019_ = _args[6];
lean_object* v___y_2020_ = _args[7];
lean_object* v___y_2021_ = _args[8];
lean_object* v___y_2022_ = _args[9];
lean_object* v___y_2023_ = _args[10];
lean_object* v___y_2024_ = _args[11];
lean_object* v___y_2025_ = _args[12];
lean_object* v___y_2026_ = _args[13];
lean_object* v___y_2027_ = _args[14];
lean_object* v___y_2028_ = _args[15];
lean_object* v___y_2029_ = _args[16];
lean_object* v___y_2030_ = _args[17];
lean_object* v___y_2031_ = _args[18];
_start:
{
size_t v_sz_boxed_2032_; size_t v_i_boxed_2033_; lean_object* v_res_2034_; 
v_sz_boxed_2032_ = lean_unbox_usize(v_sz_2017_);
lean_dec(v_sz_2017_);
v_i_boxed_2033_ = lean_unbox_usize(v_i_2018_);
lean_dec(v_i_2018_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_2013_, v_x_2014_, v_c_u2081_2015_, v_as_2016_, v_sz_boxed_2032_, v_i_boxed_2033_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec_ref(v_as_2016_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_2035_, lean_object* v_x_2036_, lean_object* v_c_u2081_2037_, lean_object* v_todo_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; size_t v_sz_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2051_ = lean_box(0);
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_2053_ = lean_array_size(v_todo_2038_);
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_2035_, v_x_2036_, v_c_u2081_2037_, v_todo_2038_, v_sz_2053_, v___x_2054_, v___x_2052_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2068_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2068_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2068_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_fst_2060_; 
v_fst_2060_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_fst_2060_);
lean_dec(v_a_2056_);
if (lean_obj_tag(v_fst_2060_) == 0)
{
lean_object* v___x_2062_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2051_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2051_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v_val_2064_; lean_object* v___x_2066_; 
v_val_2064_ = lean_ctor_get(v_fst_2060_, 0);
lean_inc(v_val_2064_);
lean_dec_ref(v_fst_2060_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_val_2064_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_val_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2055_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2055_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2077_, lean_object* v_x_2078_, lean_object* v_c_u2081_2079_, lean_object* v_todo_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2077_, v_x_2078_, v_c_u2081_2079_, v_todo_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec_ref(v_todo_2080_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2094_, lean_object* v_as_2095_, size_t v_sz_2096_, size_t v_i_2097_, lean_object* v_b_2098_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_usize_dec_lt(v_i_2097_, v_sz_2096_);
if (v___x_2099_ == 0)
{
return v_b_2098_;
}
else
{
lean_object* v_snd_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2133_; 
v_snd_2100_ = lean_ctor_get(v_b_2098_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_b_2098_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_b_2098_, 0);
lean_dec(v_unused_2134_);
v___x_2102_ = v_b_2098_;
v_isShared_2103_ = v_isSharedCheck_2133_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_snd_2100_);
lean_dec(v_b_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2133_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2132_; 
v_fst_2104_ = lean_ctor_get(v_snd_2100_, 0);
v_snd_2105_ = lean_ctor_get(v_snd_2100_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_snd_2100_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2107_ = v_snd_2100_;
v_isShared_2108_ = v_isSharedCheck_2132_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_snd_2105_);
lean_inc(v_fst_2104_);
lean_dec(v_snd_2100_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2132_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_a_2109_; lean_object* v_p_2110_; lean_object* v___x_2111_; lean_object* v_a_2113_; lean_object* v_b_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_a_2109_ = lean_array_uget_borrowed(v_as_2095_, v_i_2097_);
v_p_2110_ = lean_ctor_get(v_a_2109_, 0);
v___x_2111_ = lean_box(0);
v_b_2120_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2110_, v_x_2094_);
v___x_2121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_2122_ = lean_int_dec_eq(v_b_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2124_; 
lean_inc(v_a_2109_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v_a_2109_);
lean_ctor_set(v___x_2102_, 0, v_b_2120_);
v___x_2124_ = v___x_2102_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_b_2120_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_a_2109_);
v___x_2124_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v_todo_2125_; lean_object* v___x_2126_; 
v_todo_2125_ = lean_array_push(v_snd_2105_, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_fst_2104_);
lean_ctor_set(v___x_2126_, 1, v_todo_2125_);
v_a_2113_ = v___x_2126_;
goto v___jp_2112_;
}
}
else
{
lean_object* v_cs_x27_2128_; lean_object* v___x_2130_; 
lean_dec(v_b_2120_);
lean_inc(v_a_2109_);
v_cs_x27_2128_ = l_Lean_PersistentArray_push___redArg(v_fst_2104_, v_a_2109_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v_snd_2105_);
lean_ctor_set(v___x_2102_, 0, v_cs_x27_2128_);
v___x_2130_ = v___x_2102_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_cs_x27_2128_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_snd_2105_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v_a_2113_ = v___x_2130_;
goto v___jp_2112_;
}
}
v___jp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v_a_2113_);
lean_ctor_set(v___x_2107_, 0, v___x_2111_);
v___x_2115_ = v___x_2107_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_a_2113_);
v___x_2115_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
size_t v___x_2116_; size_t v___x_2117_; 
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_add(v_i_2097_, v___x_2116_);
v_i_2097_ = v___x_2117_;
v_b_2098_ = v___x_2115_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2135_, lean_object* v_as_2136_, lean_object* v_sz_2137_, lean_object* v_i_2138_, lean_object* v_b_2139_){
_start:
{
size_t v_sz_boxed_2140_; size_t v_i_boxed_2141_; lean_object* v_res_2142_; 
v_sz_boxed_2140_ = lean_unbox_usize(v_sz_2137_);
lean_dec(v_sz_2137_);
v_i_boxed_2141_ = lean_unbox_usize(v_i_2138_);
lean_dec(v_i_2138_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2135_, v_as_2136_, v_sz_boxed_2140_, v_i_boxed_2141_, v_b_2139_);
lean_dec_ref(v_as_2136_);
lean_dec(v_x_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2143_, lean_object* v_as_2144_, size_t v_sz_2145_, size_t v_i_2146_, lean_object* v_b_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_lt(v_i_2146_, v_sz_2145_);
if (v___x_2148_ == 0)
{
return v_b_2147_;
}
else
{
lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2182_; 
v_snd_2149_ = lean_ctor_get(v_b_2147_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v_b_2147_, 0);
lean_dec(v_unused_2183_);
v___x_2151_ = v_b_2147_;
v_isShared_2152_ = v_isSharedCheck_2182_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_dec(v_b_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2182_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_fst_2153_; lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2181_; 
v_fst_2153_ = lean_ctor_get(v_snd_2149_, 0);
v_snd_2154_ = lean_ctor_get(v_snd_2149_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_snd_2149_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2156_ = v_snd_2149_;
v_isShared_2157_ = v_isSharedCheck_2181_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_inc(v_fst_2153_);
lean_dec(v_snd_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2181_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_a_2158_; lean_object* v_p_2159_; lean_object* v___x_2160_; lean_object* v_a_2162_; lean_object* v_b_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_a_2158_ = lean_array_uget_borrowed(v_as_2144_, v_i_2146_);
v_p_2159_ = lean_ctor_get(v_a_2158_, 0);
v___x_2160_ = lean_box(0);
v_b_2169_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2159_, v_x_2143_);
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_2171_ = lean_int_dec_eq(v_b_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2173_; 
lean_inc(v_a_2158_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_a_2158_);
lean_ctor_set(v___x_2151_, 0, v_b_2169_);
v___x_2173_ = v___x_2151_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_b_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_a_2158_);
v___x_2173_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v_todo_2174_; lean_object* v___x_2175_; 
v_todo_2174_ = lean_array_push(v_snd_2154_, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v_fst_2153_);
lean_ctor_set(v___x_2175_, 1, v_todo_2174_);
v_a_2162_ = v___x_2175_;
goto v___jp_2161_;
}
}
else
{
lean_object* v_cs_x27_2177_; lean_object* v___x_2179_; 
lean_dec(v_b_2169_);
lean_inc(v_a_2158_);
v_cs_x27_2177_ = l_Lean_PersistentArray_push___redArg(v_fst_2153_, v_a_2158_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_snd_2154_);
lean_ctor_set(v___x_2151_, 0, v_cs_x27_2177_);
v___x_2179_ = v___x_2151_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_cs_x27_2177_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_snd_2154_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
v_a_2162_ = v___x_2179_;
goto v___jp_2161_;
}
}
v___jp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v_a_2162_);
lean_ctor_set(v___x_2156_, 0, v___x_2160_);
v___x_2164_ = v___x_2156_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_a_2162_);
v___x_2164_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2146_, v___x_2165_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2143_, v_as_2144_, v_sz_2145_, v___x_2166_, v___x_2164_);
return v___x_2167_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2184_, lean_object* v_as_2185_, lean_object* v_sz_2186_, lean_object* v_i_2187_, lean_object* v_b_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2186_);
lean_dec(v_sz_2186_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2184_, v_as_2185_, v_sz_boxed_2189_, v_i_boxed_2190_, v_b_2188_);
lean_dec_ref(v_as_2185_);
lean_dec(v_x_2184_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2192_, lean_object* v_as_2193_, size_t v_sz_2194_, size_t v_i_2195_, lean_object* v_b_2196_){
_start:
{
uint8_t v___x_2197_; 
v___x_2197_ = lean_usize_dec_lt(v_i_2195_, v_sz_2194_);
if (v___x_2197_ == 0)
{
return v_b_2196_;
}
else
{
lean_object* v_snd_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2231_; 
v_snd_2198_ = lean_ctor_get(v_b_2196_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_b_2196_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v_b_2196_, 0);
lean_dec(v_unused_2232_);
v___x_2200_ = v_b_2196_;
v_isShared_2201_ = v_isSharedCheck_2231_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_snd_2198_);
lean_dec(v_b_2196_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2231_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_fst_2202_; lean_object* v_snd_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2230_; 
v_fst_2202_ = lean_ctor_get(v_snd_2198_, 0);
v_snd_2203_ = lean_ctor_get(v_snd_2198_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_snd_2198_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2205_ = v_snd_2198_;
v_isShared_2206_ = v_isSharedCheck_2230_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_snd_2203_);
lean_inc(v_fst_2202_);
lean_dec(v_snd_2198_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2230_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_a_2207_; lean_object* v_p_2208_; lean_object* v___x_2209_; lean_object* v_a_2211_; lean_object* v_b_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_a_2207_ = lean_array_uget_borrowed(v_as_2193_, v_i_2195_);
v_p_2208_ = lean_ctor_get(v_a_2207_, 0);
v___x_2209_ = lean_box(0);
v_b_2218_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2208_, v_x_2192_);
v___x_2219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_2220_ = lean_int_dec_eq(v_b_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2222_; 
lean_inc(v_a_2207_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v_a_2207_);
lean_ctor_set(v___x_2200_, 0, v_b_2218_);
v___x_2222_ = v___x_2200_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_b_2218_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_a_2207_);
v___x_2222_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v_todo_2223_; lean_object* v___x_2224_; 
v_todo_2223_ = lean_array_push(v_snd_2203_, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_fst_2202_);
lean_ctor_set(v___x_2224_, 1, v_todo_2223_);
v_a_2211_ = v___x_2224_;
goto v___jp_2210_;
}
}
else
{
lean_object* v_cs_x27_2226_; lean_object* v___x_2228_; 
lean_dec(v_b_2218_);
lean_inc(v_a_2207_);
v_cs_x27_2226_ = l_Lean_PersistentArray_push___redArg(v_fst_2202_, v_a_2207_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v_snd_2203_);
lean_ctor_set(v___x_2200_, 0, v_cs_x27_2226_);
v___x_2228_ = v___x_2200_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_cs_x27_2226_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_snd_2203_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
v_a_2211_ = v___x_2228_;
goto v___jp_2210_;
}
}
v___jp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v_a_2211_);
lean_ctor_set(v___x_2205_, 0, v___x_2209_);
v___x_2213_ = v___x_2205_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_a_2211_);
v___x_2213_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
size_t v___x_2214_; size_t v___x_2215_; 
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_add(v_i_2195_, v___x_2214_);
v_i_2195_ = v___x_2215_;
v_b_2196_ = v___x_2213_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2233_, lean_object* v_as_2234_, lean_object* v_sz_2235_, lean_object* v_i_2236_, lean_object* v_b_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2235_);
lean_dec(v_sz_2235_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2233_, v_as_2234_, v_sz_boxed_2238_, v_i_boxed_2239_, v_b_2237_);
lean_dec_ref(v_as_2234_);
lean_dec(v_x_2233_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2241_, lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_){
_start:
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_usize_dec_lt(v_i_2244_, v_sz_2243_);
if (v___x_2246_ == 0)
{
return v_b_2245_;
}
else
{
lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2280_; 
v_snd_2247_ = lean_ctor_get(v_b_2245_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_b_2245_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; 
v_unused_2281_ = lean_ctor_get(v_b_2245_, 0);
lean_dec(v_unused_2281_);
v___x_2249_ = v_b_2245_;
v_isShared_2250_ = v_isSharedCheck_2280_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_dec(v_b_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2280_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_fst_2251_; lean_object* v_snd_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2279_; 
v_fst_2251_ = lean_ctor_get(v_snd_2247_, 0);
v_snd_2252_ = lean_ctor_get(v_snd_2247_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_snd_2247_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2254_ = v_snd_2247_;
v_isShared_2255_ = v_isSharedCheck_2279_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_snd_2252_);
lean_inc(v_fst_2251_);
lean_dec(v_snd_2247_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2279_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_a_2256_; lean_object* v_p_2257_; lean_object* v___x_2258_; lean_object* v_a_2260_; lean_object* v_b_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_a_2256_ = lean_array_uget_borrowed(v_as_2242_, v_i_2244_);
v_p_2257_ = lean_ctor_get(v_a_2256_, 0);
v___x_2258_ = lean_box(0);
v_b_2267_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2257_, v_x_2241_);
v___x_2268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_2269_ = lean_int_dec_eq(v_b_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2271_; 
lean_inc(v_a_2256_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_a_2256_);
lean_ctor_set(v___x_2249_, 0, v_b_2267_);
v___x_2271_ = v___x_2249_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_b_2267_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_a_2256_);
v___x_2271_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v_todo_2272_; lean_object* v___x_2273_; 
v_todo_2272_ = lean_array_push(v_snd_2252_, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_fst_2251_);
lean_ctor_set(v___x_2273_, 1, v_todo_2272_);
v_a_2260_ = v___x_2273_;
goto v___jp_2259_;
}
}
else
{
lean_object* v_cs_x27_2275_; lean_object* v___x_2277_; 
lean_dec(v_b_2267_);
lean_inc(v_a_2256_);
v_cs_x27_2275_ = l_Lean_PersistentArray_push___redArg(v_fst_2251_, v_a_2256_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_snd_2252_);
lean_ctor_set(v___x_2249_, 0, v_cs_x27_2275_);
v___x_2277_ = v___x_2249_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_cs_x27_2275_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_snd_2252_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
v_a_2260_ = v___x_2277_;
goto v___jp_2259_;
}
}
v___jp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v_a_2260_);
lean_ctor_set(v___x_2254_, 0, v___x_2258_);
v___x_2262_ = v___x_2254_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_a_2260_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2244_, v___x_2263_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2241_, v_as_2242_, v_sz_2243_, v___x_2264_, v___x_2262_);
return v___x_2265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2282_, lean_object* v_as_2283_, lean_object* v_sz_2284_, lean_object* v_i_2285_, lean_object* v_b_2286_){
_start:
{
size_t v_sz_boxed_2287_; size_t v_i_boxed_2288_; lean_object* v_res_2289_; 
v_sz_boxed_2287_ = lean_unbox_usize(v_sz_2284_);
lean_dec(v_sz_2284_);
v_i_boxed_2288_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2282_, v_as_2283_, v_sz_boxed_2287_, v_i_boxed_2288_, v_b_2286_);
lean_dec_ref(v_as_2283_);
lean_dec(v_x_2282_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_x_2290_, lean_object* v_inh_2291_, lean_object* v_n_2292_, lean_object* v_b_2293_){
_start:
{
if (lean_obj_tag(v_n_2292_) == 0)
{
lean_object* v_cs_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2309_; 
v_cs_2294_ = lean_ctor_get(v_n_2292_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_n_2292_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2296_ = v_n_2292_;
v_isShared_2297_ = v_isSharedCheck_2309_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_cs_2294_);
lean_dec(v_n_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2309_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; size_t v_sz_2300_; size_t v___x_2301_; lean_object* v___x_2302_; lean_object* v_fst_2303_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_b_2293_);
v_sz_2300_ = lean_array_size(v_cs_2294_);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2290_, v_inh_2291_, v_cs_2294_, v_sz_2300_, v___x_2301_, v___x_2299_);
lean_dec_ref(v_cs_2294_);
v_fst_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_fst_2303_);
if (lean_obj_tag(v_fst_2303_) == 0)
{
lean_object* v_snd_2304_; lean_object* v___x_2306_; 
v_snd_2304_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_snd_2304_);
lean_dec_ref(v___x_2302_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 1);
lean_ctor_set(v___x_2296_, 0, v_snd_2304_);
v___x_2306_ = v___x_2296_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_snd_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
lean_object* v_val_2308_; 
lean_dec_ref(v___x_2302_);
lean_del_object(v___x_2296_);
v_val_2308_ = lean_ctor_get(v_fst_2303_, 0);
lean_inc(v_val_2308_);
lean_dec_ref(v_fst_2303_);
return v_val_2308_;
}
}
}
else
{
lean_object* v_vs_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2325_; 
v_vs_2310_ = lean_ctor_get(v_n_2292_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_n_2292_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2312_ = v_n_2292_;
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_vs_2310_);
lean_dec(v_n_2292_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2325_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; size_t v_sz_2316_; size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v_fst_2319_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v_b_2293_);
v_sz_2316_ = lean_array_size(v_vs_2310_);
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2290_, v_vs_2310_, v_sz_2316_, v___x_2317_, v___x_2315_);
lean_dec_ref(v_vs_2310_);
v_fst_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_fst_2319_);
if (lean_obj_tag(v_fst_2319_) == 0)
{
lean_object* v_snd_2320_; lean_object* v___x_2322_; 
v_snd_2320_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_snd_2320_);
lean_dec_ref(v___x_2318_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_snd_2320_);
v___x_2322_ = v___x_2312_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_snd_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v_val_2324_; 
lean_dec_ref(v___x_2318_);
lean_del_object(v___x_2312_);
v_val_2324_ = lean_ctor_get(v_fst_2319_, 0);
lean_inc(v_val_2324_);
lean_dec_ref(v_fst_2319_);
return v_val_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2326_, lean_object* v_inh_2327_, lean_object* v_as_2328_, size_t v_sz_2329_, size_t v_i_2330_, lean_object* v_b_2331_){
_start:
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_usize_dec_lt(v_i_2330_, v_sz_2329_);
if (v___x_2332_ == 0)
{
return v_b_2331_;
}
else
{
lean_object* v_snd_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2351_; 
v_snd_2333_ = lean_ctor_get(v_b_2331_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_b_2331_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_b_2331_, 0);
lean_dec(v_unused_2352_);
v___x_2335_ = v_b_2331_;
v_isShared_2336_ = v_isSharedCheck_2351_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snd_2333_);
lean_dec(v_b_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2351_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_array_uget_borrowed(v_as_2328_, v_i_2330_);
lean_inc(v_snd_2333_);
lean_inc(v_a_2337_);
v___x_2338_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2326_, v_inh_2327_, v_a_2337_, v_snd_2333_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2339_);
v___x_2341_ = v___x_2335_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_snd_2333_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
lean_dec(v_snd_2333_);
v_a_2343_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2338_);
v___x_2344_ = lean_box(0);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v_a_2343_);
lean_ctor_set(v___x_2335_, 0, v___x_2344_);
v___x_2346_ = v___x_2335_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_a_2343_);
v___x_2346_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
size_t v___x_2347_; size_t v___x_2348_; 
v___x_2347_ = ((size_t)1ULL);
v___x_2348_ = lean_usize_add(v_i_2330_, v___x_2347_);
v_i_2330_ = v___x_2348_;
v_b_2331_ = v___x_2346_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2353_, lean_object* v_inh_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_){
_start:
{
size_t v_sz_boxed_2359_; size_t v_i_boxed_2360_; lean_object* v_res_2361_; 
v_sz_boxed_2359_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2360_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2353_, v_inh_2354_, v_as_2355_, v_sz_boxed_2359_, v_i_boxed_2360_, v_b_2358_);
lean_dec_ref(v_as_2355_);
lean_dec_ref(v_inh_2354_);
lean_dec(v_x_2353_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2362_, lean_object* v_inh_2363_, lean_object* v_n_2364_, lean_object* v_b_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2362_, v_inh_2363_, v_n_2364_, v_b_2365_);
lean_dec_ref(v_inh_2363_);
lean_dec(v_x_2362_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2367_, lean_object* v_t_2368_, lean_object* v_init_2369_){
_start:
{
lean_object* v_root_2370_; lean_object* v_tail_2371_; lean_object* v___x_2372_; 
v_root_2370_ = lean_ctor_get(v_t_2368_, 0);
lean_inc_ref(v_root_2370_);
v_tail_2371_ = lean_ctor_get(v_t_2368_, 1);
lean_inc_ref(v_tail_2371_);
lean_dec_ref(v_t_2368_);
lean_inc_ref(v_init_2369_);
v___x_2372_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2367_, v_init_2369_, v_root_2370_, v_init_2369_);
lean_dec_ref(v_init_2369_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; 
lean_dec_ref(v_tail_2371_);
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
return v_a_2373_;
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; size_t v_sz_2377_; size_t v___x_2378_; lean_object* v___x_2379_; lean_object* v_fst_2380_; 
v_a_2374_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2372_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v_a_2374_);
v_sz_2377_ = lean_array_size(v_tail_2371_);
v___x_2378_ = ((size_t)0ULL);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2367_, v_tail_2371_, v_sz_2377_, v___x_2378_, v___x_2376_);
lean_dec_ref(v_tail_2371_);
v_fst_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_fst_2380_);
if (lean_obj_tag(v_fst_2380_) == 0)
{
lean_object* v_snd_2381_; 
v_snd_2381_ = lean_ctor_get(v___x_2379_, 1);
lean_inc(v_snd_2381_);
lean_dec_ref(v___x_2379_);
return v_snd_2381_;
}
else
{
lean_object* v_val_2382_; 
lean_dec_ref(v___x_2379_);
v_val_2382_ = lean_ctor_get(v_fst_2380_, 0);
lean_inc(v_val_2382_);
lean_dec_ref(v_fst_2380_);
return v_val_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2383_, lean_object* v_t_2384_, lean_object* v_init_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2383_, v_t_2384_, v_init_2385_);
lean_dec(v_x_2383_);
return v_res_2386_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_unsigned_to_nat(32u);
v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_cs_x27_2395_; 
v___x_2390_ = ((size_t)5ULL);
v___x_2391_ = lean_unsigned_to_nat(0u);
v___x_2392_ = lean_unsigned_to_nat(32u);
v___x_2393_ = lean_mk_empty_array_with_capacity(v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2395_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2395_, 0, v___x_2394_);
lean_ctor_set(v_cs_x27_2395_, 1, v___x_2393_);
lean_ctor_set(v_cs_x27_2395_, 2, v___x_2391_);
lean_ctor_set(v_cs_x27_2395_, 3, v___x_2391_);
lean_ctor_set_usize(v_cs_x27_2395_, 4, v___x_2390_);
return v_cs_x27_2395_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2398_; lean_object* v_cs_x27_2399_; lean_object* v___x_2400_; 
v_todo_2398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2399_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v_cs_x27_2399_);
lean_ctor_set(v___x_2400_, 1, v_todo_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2401_, lean_object* v_cs_2402_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v___x_2403_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2404_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2401_, v_cs_2402_, v___x_2403_);
v_fst_2405_ = lean_ctor_get(v___x_2404_, 0);
v_snd_2406_ = lean_ctor_get(v___x_2404_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2404_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_snd_2406_);
lean_inc(v_fst_2405_);
lean_dec(v___x_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_fst_2405_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_snd_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2414_, lean_object* v_cs_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2414_, v_cs_2415_);
lean_dec(v_x_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2417_, lean_object* v_cs_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2417_, v_cs_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2420_, lean_object* v_cs_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2420_, v_cs_2421_);
lean_dec(v_x_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2423_, lean_object* v_y_2424_, lean_object* v_fst_2425_, lean_object* v_s_2426_){
_start:
{
lean_object* v_structs_2427_; lean_object* v_typeIdOf_2428_; lean_object* v_exprToStructId_2429_; lean_object* v_exprToStructIdEntries_2430_; lean_object* v_forbiddenNatModules_2431_; lean_object* v_natStructs_2432_; lean_object* v_natTypeIdOf_2433_; lean_object* v_exprToNatStructId_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_structs_2427_ = lean_ctor_get(v_s_2426_, 0);
v_typeIdOf_2428_ = lean_ctor_get(v_s_2426_, 1);
v_exprToStructId_2429_ = lean_ctor_get(v_s_2426_, 2);
v_exprToStructIdEntries_2430_ = lean_ctor_get(v_s_2426_, 3);
v_forbiddenNatModules_2431_ = lean_ctor_get(v_s_2426_, 4);
v_natStructs_2432_ = lean_ctor_get(v_s_2426_, 5);
v_natTypeIdOf_2433_ = lean_ctor_get(v_s_2426_, 6);
v_exprToNatStructId_2434_ = lean_ctor_get(v_s_2426_, 7);
v___x_2435_ = lean_array_get_size(v_structs_2427_);
v___x_2436_ = lean_nat_dec_lt(v_a_2423_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_dec_ref(v_fst_2425_);
return v_s_2426_;
}
else
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2498_; 
lean_inc_ref(v_exprToNatStructId_2434_);
lean_inc_ref(v_natTypeIdOf_2433_);
lean_inc_ref(v_natStructs_2432_);
lean_inc_ref(v_forbiddenNatModules_2431_);
lean_inc_ref(v_exprToStructIdEntries_2430_);
lean_inc_ref(v_exprToStructId_2429_);
lean_inc_ref(v_typeIdOf_2428_);
lean_inc_ref(v_structs_2427_);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_s_2426_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; 
v_unused_2499_ = lean_ctor_get(v_s_2426_, 7);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_s_2426_, 6);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_s_2426_, 5);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_s_2426_, 4);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_s_2426_, 3);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_s_2426_, 2);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_s_2426_, 1);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_s_2426_, 0);
lean_dec(v_unused_2506_);
v___x_2438_ = v_s_2426_;
v_isShared_2439_ = v_isSharedCheck_2498_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v_s_2426_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2498_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v_v_2440_; lean_object* v_id_2441_; lean_object* v_ringId_x3f_2442_; lean_object* v_type_2443_; lean_object* v_u_2444_; lean_object* v_intModuleInst_2445_; lean_object* v_leInst_x3f_2446_; lean_object* v_ltInst_x3f_2447_; lean_object* v_lawfulOrderLTInst_x3f_2448_; lean_object* v_isPreorderInst_x3f_2449_; lean_object* v_orderedAddInst_x3f_2450_; lean_object* v_isLinearInst_x3f_2451_; lean_object* v_noNatDivInst_x3f_2452_; lean_object* v_ringInst_x3f_2453_; lean_object* v_commRingInst_x3f_2454_; lean_object* v_orderedRingInst_x3f_2455_; lean_object* v_fieldInst_x3f_2456_; lean_object* v_charInst_x3f_2457_; lean_object* v_zero_2458_; lean_object* v_ofNatZero_2459_; lean_object* v_one_x3f_2460_; lean_object* v_leFn_x3f_2461_; lean_object* v_ltFn_x3f_2462_; lean_object* v_addFn_2463_; lean_object* v_zsmulFn_2464_; lean_object* v_nsmulFn_2465_; lean_object* v_zsmulFn_x3f_2466_; lean_object* v_nsmulFn_x3f_2467_; lean_object* v_homomulFn_x3f_2468_; lean_object* v_subFn_2469_; lean_object* v_negFn_2470_; lean_object* v_vars_2471_; lean_object* v_varMap_2472_; lean_object* v_lowers_2473_; lean_object* v_uppers_2474_; lean_object* v_diseqs_2475_; lean_object* v_assignment_2476_; uint8_t v_caseSplits_2477_; lean_object* v_conflict_x3f_2478_; lean_object* v_diseqSplits_2479_; lean_object* v_elimEqs_2480_; lean_object* v_elimStack_2481_; lean_object* v_occurs_2482_; lean_object* v_ignored_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2497_; 
v_v_2440_ = lean_array_fget(v_structs_2427_, v_a_2423_);
v_id_2441_ = lean_ctor_get(v_v_2440_, 0);
v_ringId_x3f_2442_ = lean_ctor_get(v_v_2440_, 1);
v_type_2443_ = lean_ctor_get(v_v_2440_, 2);
v_u_2444_ = lean_ctor_get(v_v_2440_, 3);
v_intModuleInst_2445_ = lean_ctor_get(v_v_2440_, 4);
v_leInst_x3f_2446_ = lean_ctor_get(v_v_2440_, 5);
v_ltInst_x3f_2447_ = lean_ctor_get(v_v_2440_, 6);
v_lawfulOrderLTInst_x3f_2448_ = lean_ctor_get(v_v_2440_, 7);
v_isPreorderInst_x3f_2449_ = lean_ctor_get(v_v_2440_, 8);
v_orderedAddInst_x3f_2450_ = lean_ctor_get(v_v_2440_, 9);
v_isLinearInst_x3f_2451_ = lean_ctor_get(v_v_2440_, 10);
v_noNatDivInst_x3f_2452_ = lean_ctor_get(v_v_2440_, 11);
v_ringInst_x3f_2453_ = lean_ctor_get(v_v_2440_, 12);
v_commRingInst_x3f_2454_ = lean_ctor_get(v_v_2440_, 13);
v_orderedRingInst_x3f_2455_ = lean_ctor_get(v_v_2440_, 14);
v_fieldInst_x3f_2456_ = lean_ctor_get(v_v_2440_, 15);
v_charInst_x3f_2457_ = lean_ctor_get(v_v_2440_, 16);
v_zero_2458_ = lean_ctor_get(v_v_2440_, 17);
v_ofNatZero_2459_ = lean_ctor_get(v_v_2440_, 18);
v_one_x3f_2460_ = lean_ctor_get(v_v_2440_, 19);
v_leFn_x3f_2461_ = lean_ctor_get(v_v_2440_, 20);
v_ltFn_x3f_2462_ = lean_ctor_get(v_v_2440_, 21);
v_addFn_2463_ = lean_ctor_get(v_v_2440_, 22);
v_zsmulFn_2464_ = lean_ctor_get(v_v_2440_, 23);
v_nsmulFn_2465_ = lean_ctor_get(v_v_2440_, 24);
v_zsmulFn_x3f_2466_ = lean_ctor_get(v_v_2440_, 25);
v_nsmulFn_x3f_2467_ = lean_ctor_get(v_v_2440_, 26);
v_homomulFn_x3f_2468_ = lean_ctor_get(v_v_2440_, 27);
v_subFn_2469_ = lean_ctor_get(v_v_2440_, 28);
v_negFn_2470_ = lean_ctor_get(v_v_2440_, 29);
v_vars_2471_ = lean_ctor_get(v_v_2440_, 30);
v_varMap_2472_ = lean_ctor_get(v_v_2440_, 31);
v_lowers_2473_ = lean_ctor_get(v_v_2440_, 32);
v_uppers_2474_ = lean_ctor_get(v_v_2440_, 33);
v_diseqs_2475_ = lean_ctor_get(v_v_2440_, 34);
v_assignment_2476_ = lean_ctor_get(v_v_2440_, 35);
v_caseSplits_2477_ = lean_ctor_get_uint8(v_v_2440_, sizeof(void*)*42);
v_conflict_x3f_2478_ = lean_ctor_get(v_v_2440_, 36);
v_diseqSplits_2479_ = lean_ctor_get(v_v_2440_, 37);
v_elimEqs_2480_ = lean_ctor_get(v_v_2440_, 38);
v_elimStack_2481_ = lean_ctor_get(v_v_2440_, 39);
v_occurs_2482_ = lean_ctor_get(v_v_2440_, 40);
v_ignored_2483_ = lean_ctor_get(v_v_2440_, 41);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_v_2440_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2485_ = v_v_2440_;
v_isShared_2486_ = v_isSharedCheck_2497_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_ignored_2483_);
lean_inc(v_occurs_2482_);
lean_inc(v_elimStack_2481_);
lean_inc(v_elimEqs_2480_);
lean_inc(v_diseqSplits_2479_);
lean_inc(v_conflict_x3f_2478_);
lean_inc(v_assignment_2476_);
lean_inc(v_diseqs_2475_);
lean_inc(v_uppers_2474_);
lean_inc(v_lowers_2473_);
lean_inc(v_varMap_2472_);
lean_inc(v_vars_2471_);
lean_inc(v_negFn_2470_);
lean_inc(v_subFn_2469_);
lean_inc(v_homomulFn_x3f_2468_);
lean_inc(v_nsmulFn_x3f_2467_);
lean_inc(v_zsmulFn_x3f_2466_);
lean_inc(v_nsmulFn_2465_);
lean_inc(v_zsmulFn_2464_);
lean_inc(v_addFn_2463_);
lean_inc(v_ltFn_x3f_2462_);
lean_inc(v_leFn_x3f_2461_);
lean_inc(v_one_x3f_2460_);
lean_inc(v_ofNatZero_2459_);
lean_inc(v_zero_2458_);
lean_inc(v_charInst_x3f_2457_);
lean_inc(v_fieldInst_x3f_2456_);
lean_inc(v_orderedRingInst_x3f_2455_);
lean_inc(v_commRingInst_x3f_2454_);
lean_inc(v_ringInst_x3f_2453_);
lean_inc(v_noNatDivInst_x3f_2452_);
lean_inc(v_isLinearInst_x3f_2451_);
lean_inc(v_orderedAddInst_x3f_2450_);
lean_inc(v_isPreorderInst_x3f_2449_);
lean_inc(v_lawfulOrderLTInst_x3f_2448_);
lean_inc(v_ltInst_x3f_2447_);
lean_inc(v_leInst_x3f_2446_);
lean_inc(v_intModuleInst_2445_);
lean_inc(v_u_2444_);
lean_inc(v_type_2443_);
lean_inc(v_ringId_x3f_2442_);
lean_inc(v_id_2441_);
lean_dec(v_v_2440_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2497_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v_xs_x27_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2487_ = lean_box(0);
v_xs_x27_2488_ = lean_array_fset(v_structs_2427_, v_a_2423_, v___x_2487_);
v___x_2489_ = l_Lean_PersistentArray_set___redArg(v_lowers_2473_, v_y_2424_, v_fst_2425_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 32, v___x_2489_);
v___x_2491_ = v___x_2485_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_id_2441_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_ringId_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_type_2443_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_u_2444_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_intModuleInst_2445_);
lean_ctor_set(v_reuseFailAlloc_2496_, 5, v_leInst_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2496_, 6, v_ltInst_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2496_, 7, v_lawfulOrderLTInst_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2496_, 8, v_isPreorderInst_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2496_, 9, v_orderedAddInst_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2496_, 10, v_isLinearInst_x3f_2451_);
lean_ctor_set(v_reuseFailAlloc_2496_, 11, v_noNatDivInst_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2496_, 12, v_ringInst_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2496_, 13, v_commRingInst_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2496_, 14, v_orderedRingInst_x3f_2455_);
lean_ctor_set(v_reuseFailAlloc_2496_, 15, v_fieldInst_x3f_2456_);
lean_ctor_set(v_reuseFailAlloc_2496_, 16, v_charInst_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2496_, 17, v_zero_2458_);
lean_ctor_set(v_reuseFailAlloc_2496_, 18, v_ofNatZero_2459_);
lean_ctor_set(v_reuseFailAlloc_2496_, 19, v_one_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2496_, 20, v_leFn_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2496_, 21, v_ltFn_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2496_, 22, v_addFn_2463_);
lean_ctor_set(v_reuseFailAlloc_2496_, 23, v_zsmulFn_2464_);
lean_ctor_set(v_reuseFailAlloc_2496_, 24, v_nsmulFn_2465_);
lean_ctor_set(v_reuseFailAlloc_2496_, 25, v_zsmulFn_x3f_2466_);
lean_ctor_set(v_reuseFailAlloc_2496_, 26, v_nsmulFn_x3f_2467_);
lean_ctor_set(v_reuseFailAlloc_2496_, 27, v_homomulFn_x3f_2468_);
lean_ctor_set(v_reuseFailAlloc_2496_, 28, v_subFn_2469_);
lean_ctor_set(v_reuseFailAlloc_2496_, 29, v_negFn_2470_);
lean_ctor_set(v_reuseFailAlloc_2496_, 30, v_vars_2471_);
lean_ctor_set(v_reuseFailAlloc_2496_, 31, v_varMap_2472_);
lean_ctor_set(v_reuseFailAlloc_2496_, 32, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2496_, 33, v_uppers_2474_);
lean_ctor_set(v_reuseFailAlloc_2496_, 34, v_diseqs_2475_);
lean_ctor_set(v_reuseFailAlloc_2496_, 35, v_assignment_2476_);
lean_ctor_set(v_reuseFailAlloc_2496_, 36, v_conflict_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2496_, 37, v_diseqSplits_2479_);
lean_ctor_set(v_reuseFailAlloc_2496_, 38, v_elimEqs_2480_);
lean_ctor_set(v_reuseFailAlloc_2496_, 39, v_elimStack_2481_);
lean_ctor_set(v_reuseFailAlloc_2496_, 40, v_occurs_2482_);
lean_ctor_set(v_reuseFailAlloc_2496_, 41, v_ignored_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2496_, sizeof(void*)*42, v_caseSplits_2477_);
v___x_2491_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = lean_array_fset(v_xs_x27_2488_, v_a_2423_, v___x_2491_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2492_);
v___x_2494_ = v___x_2438_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_typeIdOf_2428_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_exprToStructId_2429_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_exprToStructIdEntries_2430_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_forbiddenNatModules_2431_);
lean_ctor_set(v_reuseFailAlloc_2495_, 5, v_natStructs_2432_);
lean_ctor_set(v_reuseFailAlloc_2495_, 6, v_natTypeIdOf_2433_);
lean_ctor_set(v_reuseFailAlloc_2495_, 7, v_exprToNatStructId_2434_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2507_, lean_object* v_y_2508_, lean_object* v_fst_2509_, lean_object* v_s_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2507_, v_y_2508_, v_fst_2509_, v_s_2510_);
lean_dec(v_y_2508_);
lean_dec(v_a_2507_);
return v_res_2511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2513_, lean_object* v_x_2514_, lean_object* v_c_2515_, lean_object* v_y_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2564_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2564_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2564_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_unbox(v_a_2530_);
lean_dec(v_a_2530_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_del_object(v___x_2532_);
v___x_2535_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___y_2538_; lean_object* v_lowers_2546_; lean_object* v_size_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v_lowers_2546_ = lean_ctor_get(v_a_2536_, 32);
lean_inc_ref(v_lowers_2546_);
lean_dec(v_a_2536_);
v_size_2547_ = lean_ctor_get(v_lowers_2546_, 2);
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2549_ = lean_nat_dec_lt(v_y_2516_, v_size_2547_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref(v_lowers_2546_);
v___x_2550_ = l_outOfBounds___redArg(v___x_2548_);
v___y_2538_ = v___x_2550_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2548_, v_lowers_2546_, v_y_2516_);
v___y_2538_ = v___x_2551_;
goto v___jp_2537_;
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2539_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2514_, v___y_2538_);
v_fst_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_fst_2540_);
v_snd_2541_ = lean_ctor_get(v___x_2539_, 1);
lean_inc(v_snd_2541_);
lean_dec_ref(v___x_2539_);
lean_inc(v_a_2517_);
v___f_2542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2542_, 0, v_a_2517_);
lean_closure_set(v___f_2542_, 1, v_y_2516_);
lean_closure_set(v___f_2542_, 2, v_fst_2540_);
v___x_2543_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2544_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2543_, v___f_2542_, v_a_2518_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref(v___x_2544_);
v___x_2545_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2513_, v_x_2514_, v_c_2515_, v_snd_2541_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_snd_2541_);
return v___x_2545_;
}
else
{
lean_dec(v_snd_2541_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_c_2515_);
lean_dec(v_x_2514_);
lean_dec(v_a_2513_);
return v___x_2544_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_y_2516_);
lean_dec_ref(v_c_2515_);
lean_dec(v_x_2514_);
lean_dec(v_a_2513_);
v_a_2552_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2535_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2535_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_y_2516_);
lean_dec_ref(v_c_2515_);
lean_dec(v_x_2514_);
lean_dec(v_a_2513_);
v___x_2560_ = lean_box(0);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2560_);
v___x_2562_ = v___x_2532_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_y_2516_);
lean_dec_ref(v_c_2515_);
lean_dec(v_x_2514_);
lean_dec(v_a_2513_);
v_a_2565_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2529_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2529_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2573_, lean_object* v_x_2574_, lean_object* v_c_2575_, lean_object* v_y_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2573_, v_x_2574_, v_c_2575_, v_y_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2590_, lean_object* v_y_2591_, lean_object* v_fst_2592_, lean_object* v_s_2593_){
_start:
{
lean_object* v_structs_2594_; lean_object* v_typeIdOf_2595_; lean_object* v_exprToStructId_2596_; lean_object* v_exprToStructIdEntries_2597_; lean_object* v_forbiddenNatModules_2598_; lean_object* v_natStructs_2599_; lean_object* v_natTypeIdOf_2600_; lean_object* v_exprToNatStructId_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v_structs_2594_ = lean_ctor_get(v_s_2593_, 0);
v_typeIdOf_2595_ = lean_ctor_get(v_s_2593_, 1);
v_exprToStructId_2596_ = lean_ctor_get(v_s_2593_, 2);
v_exprToStructIdEntries_2597_ = lean_ctor_get(v_s_2593_, 3);
v_forbiddenNatModules_2598_ = lean_ctor_get(v_s_2593_, 4);
v_natStructs_2599_ = lean_ctor_get(v_s_2593_, 5);
v_natTypeIdOf_2600_ = lean_ctor_get(v_s_2593_, 6);
v_exprToNatStructId_2601_ = lean_ctor_get(v_s_2593_, 7);
v___x_2602_ = lean_array_get_size(v_structs_2594_);
v___x_2603_ = lean_nat_dec_lt(v_a_2590_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_dec_ref(v_fst_2592_);
return v_s_2593_;
}
else
{
lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2665_; 
lean_inc_ref(v_exprToNatStructId_2601_);
lean_inc_ref(v_natTypeIdOf_2600_);
lean_inc_ref(v_natStructs_2599_);
lean_inc_ref(v_forbiddenNatModules_2598_);
lean_inc_ref(v_exprToStructIdEntries_2597_);
lean_inc_ref(v_exprToStructId_2596_);
lean_inc_ref(v_typeIdOf_2595_);
lean_inc_ref(v_structs_2594_);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_s_2593_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; lean_object* v_unused_2667_; lean_object* v_unused_2668_; lean_object* v_unused_2669_; lean_object* v_unused_2670_; lean_object* v_unused_2671_; lean_object* v_unused_2672_; lean_object* v_unused_2673_; 
v_unused_2666_ = lean_ctor_get(v_s_2593_, 7);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_s_2593_, 6);
lean_dec(v_unused_2667_);
v_unused_2668_ = lean_ctor_get(v_s_2593_, 5);
lean_dec(v_unused_2668_);
v_unused_2669_ = lean_ctor_get(v_s_2593_, 4);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_s_2593_, 3);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_s_2593_, 2);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_s_2593_, 1);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_s_2593_, 0);
lean_dec(v_unused_2673_);
v___x_2605_ = v_s_2593_;
v_isShared_2606_ = v_isSharedCheck_2665_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v_s_2593_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2665_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_v_2607_; lean_object* v_id_2608_; lean_object* v_ringId_x3f_2609_; lean_object* v_type_2610_; lean_object* v_u_2611_; lean_object* v_intModuleInst_2612_; lean_object* v_leInst_x3f_2613_; lean_object* v_ltInst_x3f_2614_; lean_object* v_lawfulOrderLTInst_x3f_2615_; lean_object* v_isPreorderInst_x3f_2616_; lean_object* v_orderedAddInst_x3f_2617_; lean_object* v_isLinearInst_x3f_2618_; lean_object* v_noNatDivInst_x3f_2619_; lean_object* v_ringInst_x3f_2620_; lean_object* v_commRingInst_x3f_2621_; lean_object* v_orderedRingInst_x3f_2622_; lean_object* v_fieldInst_x3f_2623_; lean_object* v_charInst_x3f_2624_; lean_object* v_zero_2625_; lean_object* v_ofNatZero_2626_; lean_object* v_one_x3f_2627_; lean_object* v_leFn_x3f_2628_; lean_object* v_ltFn_x3f_2629_; lean_object* v_addFn_2630_; lean_object* v_zsmulFn_2631_; lean_object* v_nsmulFn_2632_; lean_object* v_zsmulFn_x3f_2633_; lean_object* v_nsmulFn_x3f_2634_; lean_object* v_homomulFn_x3f_2635_; lean_object* v_subFn_2636_; lean_object* v_negFn_2637_; lean_object* v_vars_2638_; lean_object* v_varMap_2639_; lean_object* v_lowers_2640_; lean_object* v_uppers_2641_; lean_object* v_diseqs_2642_; lean_object* v_assignment_2643_; uint8_t v_caseSplits_2644_; lean_object* v_conflict_x3f_2645_; lean_object* v_diseqSplits_2646_; lean_object* v_elimEqs_2647_; lean_object* v_elimStack_2648_; lean_object* v_occurs_2649_; lean_object* v_ignored_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2664_; 
v_v_2607_ = lean_array_fget(v_structs_2594_, v_a_2590_);
v_id_2608_ = lean_ctor_get(v_v_2607_, 0);
v_ringId_x3f_2609_ = lean_ctor_get(v_v_2607_, 1);
v_type_2610_ = lean_ctor_get(v_v_2607_, 2);
v_u_2611_ = lean_ctor_get(v_v_2607_, 3);
v_intModuleInst_2612_ = lean_ctor_get(v_v_2607_, 4);
v_leInst_x3f_2613_ = lean_ctor_get(v_v_2607_, 5);
v_ltInst_x3f_2614_ = lean_ctor_get(v_v_2607_, 6);
v_lawfulOrderLTInst_x3f_2615_ = lean_ctor_get(v_v_2607_, 7);
v_isPreorderInst_x3f_2616_ = lean_ctor_get(v_v_2607_, 8);
v_orderedAddInst_x3f_2617_ = lean_ctor_get(v_v_2607_, 9);
v_isLinearInst_x3f_2618_ = lean_ctor_get(v_v_2607_, 10);
v_noNatDivInst_x3f_2619_ = lean_ctor_get(v_v_2607_, 11);
v_ringInst_x3f_2620_ = lean_ctor_get(v_v_2607_, 12);
v_commRingInst_x3f_2621_ = lean_ctor_get(v_v_2607_, 13);
v_orderedRingInst_x3f_2622_ = lean_ctor_get(v_v_2607_, 14);
v_fieldInst_x3f_2623_ = lean_ctor_get(v_v_2607_, 15);
v_charInst_x3f_2624_ = lean_ctor_get(v_v_2607_, 16);
v_zero_2625_ = lean_ctor_get(v_v_2607_, 17);
v_ofNatZero_2626_ = lean_ctor_get(v_v_2607_, 18);
v_one_x3f_2627_ = lean_ctor_get(v_v_2607_, 19);
v_leFn_x3f_2628_ = lean_ctor_get(v_v_2607_, 20);
v_ltFn_x3f_2629_ = lean_ctor_get(v_v_2607_, 21);
v_addFn_2630_ = lean_ctor_get(v_v_2607_, 22);
v_zsmulFn_2631_ = lean_ctor_get(v_v_2607_, 23);
v_nsmulFn_2632_ = lean_ctor_get(v_v_2607_, 24);
v_zsmulFn_x3f_2633_ = lean_ctor_get(v_v_2607_, 25);
v_nsmulFn_x3f_2634_ = lean_ctor_get(v_v_2607_, 26);
v_homomulFn_x3f_2635_ = lean_ctor_get(v_v_2607_, 27);
v_subFn_2636_ = lean_ctor_get(v_v_2607_, 28);
v_negFn_2637_ = lean_ctor_get(v_v_2607_, 29);
v_vars_2638_ = lean_ctor_get(v_v_2607_, 30);
v_varMap_2639_ = lean_ctor_get(v_v_2607_, 31);
v_lowers_2640_ = lean_ctor_get(v_v_2607_, 32);
v_uppers_2641_ = lean_ctor_get(v_v_2607_, 33);
v_diseqs_2642_ = lean_ctor_get(v_v_2607_, 34);
v_assignment_2643_ = lean_ctor_get(v_v_2607_, 35);
v_caseSplits_2644_ = lean_ctor_get_uint8(v_v_2607_, sizeof(void*)*42);
v_conflict_x3f_2645_ = lean_ctor_get(v_v_2607_, 36);
v_diseqSplits_2646_ = lean_ctor_get(v_v_2607_, 37);
v_elimEqs_2647_ = lean_ctor_get(v_v_2607_, 38);
v_elimStack_2648_ = lean_ctor_get(v_v_2607_, 39);
v_occurs_2649_ = lean_ctor_get(v_v_2607_, 40);
v_ignored_2650_ = lean_ctor_get(v_v_2607_, 41);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_v_2607_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2652_ = v_v_2607_;
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_ignored_2650_);
lean_inc(v_occurs_2649_);
lean_inc(v_elimStack_2648_);
lean_inc(v_elimEqs_2647_);
lean_inc(v_diseqSplits_2646_);
lean_inc(v_conflict_x3f_2645_);
lean_inc(v_assignment_2643_);
lean_inc(v_diseqs_2642_);
lean_inc(v_uppers_2641_);
lean_inc(v_lowers_2640_);
lean_inc(v_varMap_2639_);
lean_inc(v_vars_2638_);
lean_inc(v_negFn_2637_);
lean_inc(v_subFn_2636_);
lean_inc(v_homomulFn_x3f_2635_);
lean_inc(v_nsmulFn_x3f_2634_);
lean_inc(v_zsmulFn_x3f_2633_);
lean_inc(v_nsmulFn_2632_);
lean_inc(v_zsmulFn_2631_);
lean_inc(v_addFn_2630_);
lean_inc(v_ltFn_x3f_2629_);
lean_inc(v_leFn_x3f_2628_);
lean_inc(v_one_x3f_2627_);
lean_inc(v_ofNatZero_2626_);
lean_inc(v_zero_2625_);
lean_inc(v_charInst_x3f_2624_);
lean_inc(v_fieldInst_x3f_2623_);
lean_inc(v_orderedRingInst_x3f_2622_);
lean_inc(v_commRingInst_x3f_2621_);
lean_inc(v_ringInst_x3f_2620_);
lean_inc(v_noNatDivInst_x3f_2619_);
lean_inc(v_isLinearInst_x3f_2618_);
lean_inc(v_orderedAddInst_x3f_2617_);
lean_inc(v_isPreorderInst_x3f_2616_);
lean_inc(v_lawfulOrderLTInst_x3f_2615_);
lean_inc(v_ltInst_x3f_2614_);
lean_inc(v_leInst_x3f_2613_);
lean_inc(v_intModuleInst_2612_);
lean_inc(v_u_2611_);
lean_inc(v_type_2610_);
lean_inc(v_ringId_x3f_2609_);
lean_inc(v_id_2608_);
lean_dec(v_v_2607_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v_xs_x27_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2654_ = lean_box(0);
v_xs_x27_2655_ = lean_array_fset(v_structs_2594_, v_a_2590_, v___x_2654_);
v___x_2656_ = l_Lean_PersistentArray_set___redArg(v_uppers_2641_, v_y_2591_, v_fst_2592_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 33, v___x_2656_);
v___x_2658_ = v___x_2652_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_id_2608_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_ringId_x3f_2609_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_type_2610_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_u_2611_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_intModuleInst_2612_);
lean_ctor_set(v_reuseFailAlloc_2663_, 5, v_leInst_x3f_2613_);
lean_ctor_set(v_reuseFailAlloc_2663_, 6, v_ltInst_x3f_2614_);
lean_ctor_set(v_reuseFailAlloc_2663_, 7, v_lawfulOrderLTInst_x3f_2615_);
lean_ctor_set(v_reuseFailAlloc_2663_, 8, v_isPreorderInst_x3f_2616_);
lean_ctor_set(v_reuseFailAlloc_2663_, 9, v_orderedAddInst_x3f_2617_);
lean_ctor_set(v_reuseFailAlloc_2663_, 10, v_isLinearInst_x3f_2618_);
lean_ctor_set(v_reuseFailAlloc_2663_, 11, v_noNatDivInst_x3f_2619_);
lean_ctor_set(v_reuseFailAlloc_2663_, 12, v_ringInst_x3f_2620_);
lean_ctor_set(v_reuseFailAlloc_2663_, 13, v_commRingInst_x3f_2621_);
lean_ctor_set(v_reuseFailAlloc_2663_, 14, v_orderedRingInst_x3f_2622_);
lean_ctor_set(v_reuseFailAlloc_2663_, 15, v_fieldInst_x3f_2623_);
lean_ctor_set(v_reuseFailAlloc_2663_, 16, v_charInst_x3f_2624_);
lean_ctor_set(v_reuseFailAlloc_2663_, 17, v_zero_2625_);
lean_ctor_set(v_reuseFailAlloc_2663_, 18, v_ofNatZero_2626_);
lean_ctor_set(v_reuseFailAlloc_2663_, 19, v_one_x3f_2627_);
lean_ctor_set(v_reuseFailAlloc_2663_, 20, v_leFn_x3f_2628_);
lean_ctor_set(v_reuseFailAlloc_2663_, 21, v_ltFn_x3f_2629_);
lean_ctor_set(v_reuseFailAlloc_2663_, 22, v_addFn_2630_);
lean_ctor_set(v_reuseFailAlloc_2663_, 23, v_zsmulFn_2631_);
lean_ctor_set(v_reuseFailAlloc_2663_, 24, v_nsmulFn_2632_);
lean_ctor_set(v_reuseFailAlloc_2663_, 25, v_zsmulFn_x3f_2633_);
lean_ctor_set(v_reuseFailAlloc_2663_, 26, v_nsmulFn_x3f_2634_);
lean_ctor_set(v_reuseFailAlloc_2663_, 27, v_homomulFn_x3f_2635_);
lean_ctor_set(v_reuseFailAlloc_2663_, 28, v_subFn_2636_);
lean_ctor_set(v_reuseFailAlloc_2663_, 29, v_negFn_2637_);
lean_ctor_set(v_reuseFailAlloc_2663_, 30, v_vars_2638_);
lean_ctor_set(v_reuseFailAlloc_2663_, 31, v_varMap_2639_);
lean_ctor_set(v_reuseFailAlloc_2663_, 32, v_lowers_2640_);
lean_ctor_set(v_reuseFailAlloc_2663_, 33, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2663_, 34, v_diseqs_2642_);
lean_ctor_set(v_reuseFailAlloc_2663_, 35, v_assignment_2643_);
lean_ctor_set(v_reuseFailAlloc_2663_, 36, v_conflict_x3f_2645_);
lean_ctor_set(v_reuseFailAlloc_2663_, 37, v_diseqSplits_2646_);
lean_ctor_set(v_reuseFailAlloc_2663_, 38, v_elimEqs_2647_);
lean_ctor_set(v_reuseFailAlloc_2663_, 39, v_elimStack_2648_);
lean_ctor_set(v_reuseFailAlloc_2663_, 40, v_occurs_2649_);
lean_ctor_set(v_reuseFailAlloc_2663_, 41, v_ignored_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*42, v_caseSplits_2644_);
v___x_2658_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_array_fset(v_xs_x27_2655_, v_a_2590_, v___x_2658_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2659_);
v___x_2661_ = v___x_2605_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_typeIdOf_2595_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_exprToStructId_2596_);
lean_ctor_set(v_reuseFailAlloc_2662_, 3, v_exprToStructIdEntries_2597_);
lean_ctor_set(v_reuseFailAlloc_2662_, 4, v_forbiddenNatModules_2598_);
lean_ctor_set(v_reuseFailAlloc_2662_, 5, v_natStructs_2599_);
lean_ctor_set(v_reuseFailAlloc_2662_, 6, v_natTypeIdOf_2600_);
lean_ctor_set(v_reuseFailAlloc_2662_, 7, v_exprToNatStructId_2601_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2674_, lean_object* v_y_2675_, lean_object* v_fst_2676_, lean_object* v_s_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2674_, v_y_2675_, v_fst_2676_, v_s_2677_);
lean_dec(v_y_2675_);
lean_dec(v_a_2674_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2679_, lean_object* v_x_2680_, lean_object* v_c_2681_, lean_object* v_y_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2730_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2730_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2730_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_unbox(v_a_2696_);
lean_dec(v_a_2696_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_del_object(v___x_2698_);
v___x_2701_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___y_2704_; lean_object* v_uppers_2712_; lean_object* v_size_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v_uppers_2712_ = lean_ctor_get(v_a_2702_, 33);
lean_inc_ref(v_uppers_2712_);
lean_dec(v_a_2702_);
v_size_2713_ = lean_ctor_get(v_uppers_2712_, 2);
v___x_2714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2715_ = lean_nat_dec_lt(v_y_2682_, v_size_2713_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_dec_ref(v_uppers_2712_);
v___x_2716_ = l_outOfBounds___redArg(v___x_2714_);
v___y_2704_ = v___x_2716_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2714_, v_uppers_2712_, v_y_2682_);
v___y_2704_ = v___x_2717_;
goto v___jp_2703_;
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v_fst_2706_; lean_object* v_snd_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2705_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2680_, v___y_2704_);
v_fst_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_fst_2706_);
v_snd_2707_ = lean_ctor_get(v___x_2705_, 1);
lean_inc(v_snd_2707_);
lean_dec_ref(v___x_2705_);
lean_inc(v_a_2683_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2708_, 0, v_a_2683_);
lean_closure_set(v___f_2708_, 1, v_y_2682_);
lean_closure_set(v___f_2708_, 2, v_fst_2706_);
v___x_2709_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2710_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2709_, v___f_2708_, v_a_2684_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2711_; 
lean_dec_ref(v___x_2710_);
v___x_2711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2679_, v_x_2680_, v_c_2681_, v_snd_2707_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_snd_2707_);
return v___x_2711_;
}
else
{
lean_dec(v_snd_2707_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_c_2681_);
lean_dec(v_x_2680_);
lean_dec(v_a_2679_);
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec(v_y_2682_);
lean_dec_ref(v_c_2681_);
lean_dec(v_x_2680_);
lean_dec(v_a_2679_);
v_a_2718_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2701_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2701_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec(v_y_2682_);
lean_dec_ref(v_c_2681_);
lean_dec(v_x_2680_);
lean_dec(v_a_2679_);
v___x_2726_ = lean_box(0);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2726_);
v___x_2728_ = v___x_2698_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec(v_y_2682_);
lean_dec_ref(v_c_2681_);
lean_dec(v_x_2680_);
lean_dec(v_a_2679_);
v_a_2731_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2695_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2695_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2739_, lean_object* v_x_2740_, lean_object* v_c_2741_, lean_object* v_y_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2739_, v_x_2740_, v_c_2741_, v_y_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2756_, lean_object* v_a_2757_, lean_object* v_s_2758_){
_start:
{
lean_object* v_structs_2759_; lean_object* v_typeIdOf_2760_; lean_object* v_exprToStructId_2761_; lean_object* v_exprToStructIdEntries_2762_; lean_object* v_forbiddenNatModules_2763_; lean_object* v_natStructs_2764_; lean_object* v_natTypeIdOf_2765_; lean_object* v_exprToNatStructId_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_structs_2759_ = lean_ctor_get(v_s_2758_, 0);
v_typeIdOf_2760_ = lean_ctor_get(v_s_2758_, 1);
v_exprToStructId_2761_ = lean_ctor_get(v_s_2758_, 2);
v_exprToStructIdEntries_2762_ = lean_ctor_get(v_s_2758_, 3);
v_forbiddenNatModules_2763_ = lean_ctor_get(v_s_2758_, 4);
v_natStructs_2764_ = lean_ctor_get(v_s_2758_, 5);
v_natTypeIdOf_2765_ = lean_ctor_get(v_s_2758_, 6);
v_exprToNatStructId_2766_ = lean_ctor_get(v_s_2758_, 7);
v___x_2767_ = lean_array_get_size(v_structs_2759_);
v___x_2768_ = lean_nat_dec_lt(v___y_2756_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec_ref(v_a_2757_);
return v_s_2758_;
}
else
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2830_; 
lean_inc_ref(v_exprToNatStructId_2766_);
lean_inc_ref(v_natTypeIdOf_2765_);
lean_inc_ref(v_natStructs_2764_);
lean_inc_ref(v_forbiddenNatModules_2763_);
lean_inc_ref(v_exprToStructIdEntries_2762_);
lean_inc_ref(v_exprToStructId_2761_);
lean_inc_ref(v_typeIdOf_2760_);
lean_inc_ref(v_structs_2759_);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_s_2758_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; lean_object* v_unused_2832_; lean_object* v_unused_2833_; lean_object* v_unused_2834_; lean_object* v_unused_2835_; lean_object* v_unused_2836_; lean_object* v_unused_2837_; lean_object* v_unused_2838_; 
v_unused_2831_ = lean_ctor_get(v_s_2758_, 7);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_s_2758_, 6);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_s_2758_, 5);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v_s_2758_, 4);
lean_dec(v_unused_2834_);
v_unused_2835_ = lean_ctor_get(v_s_2758_, 3);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_s_2758_, 2);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_s_2758_, 1);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_s_2758_, 0);
lean_dec(v_unused_2838_);
v___x_2770_ = v_s_2758_;
v_isShared_2771_ = v_isSharedCheck_2830_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_s_2758_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2830_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_v_2772_; lean_object* v_id_2773_; lean_object* v_ringId_x3f_2774_; lean_object* v_type_2775_; lean_object* v_u_2776_; lean_object* v_intModuleInst_2777_; lean_object* v_leInst_x3f_2778_; lean_object* v_ltInst_x3f_2779_; lean_object* v_lawfulOrderLTInst_x3f_2780_; lean_object* v_isPreorderInst_x3f_2781_; lean_object* v_orderedAddInst_x3f_2782_; lean_object* v_isLinearInst_x3f_2783_; lean_object* v_noNatDivInst_x3f_2784_; lean_object* v_ringInst_x3f_2785_; lean_object* v_commRingInst_x3f_2786_; lean_object* v_orderedRingInst_x3f_2787_; lean_object* v_fieldInst_x3f_2788_; lean_object* v_charInst_x3f_2789_; lean_object* v_zero_2790_; lean_object* v_ofNatZero_2791_; lean_object* v_one_x3f_2792_; lean_object* v_leFn_x3f_2793_; lean_object* v_ltFn_x3f_2794_; lean_object* v_addFn_2795_; lean_object* v_zsmulFn_2796_; lean_object* v_nsmulFn_2797_; lean_object* v_zsmulFn_x3f_2798_; lean_object* v_nsmulFn_x3f_2799_; lean_object* v_homomulFn_x3f_2800_; lean_object* v_subFn_2801_; lean_object* v_negFn_2802_; lean_object* v_vars_2803_; lean_object* v_varMap_2804_; lean_object* v_lowers_2805_; lean_object* v_uppers_2806_; lean_object* v_diseqs_2807_; lean_object* v_assignment_2808_; uint8_t v_caseSplits_2809_; lean_object* v_conflict_x3f_2810_; lean_object* v_diseqSplits_2811_; lean_object* v_elimEqs_2812_; lean_object* v_elimStack_2813_; lean_object* v_occurs_2814_; lean_object* v_ignored_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2829_; 
v_v_2772_ = lean_array_fget(v_structs_2759_, v___y_2756_);
v_id_2773_ = lean_ctor_get(v_v_2772_, 0);
v_ringId_x3f_2774_ = lean_ctor_get(v_v_2772_, 1);
v_type_2775_ = lean_ctor_get(v_v_2772_, 2);
v_u_2776_ = lean_ctor_get(v_v_2772_, 3);
v_intModuleInst_2777_ = lean_ctor_get(v_v_2772_, 4);
v_leInst_x3f_2778_ = lean_ctor_get(v_v_2772_, 5);
v_ltInst_x3f_2779_ = lean_ctor_get(v_v_2772_, 6);
v_lawfulOrderLTInst_x3f_2780_ = lean_ctor_get(v_v_2772_, 7);
v_isPreorderInst_x3f_2781_ = lean_ctor_get(v_v_2772_, 8);
v_orderedAddInst_x3f_2782_ = lean_ctor_get(v_v_2772_, 9);
v_isLinearInst_x3f_2783_ = lean_ctor_get(v_v_2772_, 10);
v_noNatDivInst_x3f_2784_ = lean_ctor_get(v_v_2772_, 11);
v_ringInst_x3f_2785_ = lean_ctor_get(v_v_2772_, 12);
v_commRingInst_x3f_2786_ = lean_ctor_get(v_v_2772_, 13);
v_orderedRingInst_x3f_2787_ = lean_ctor_get(v_v_2772_, 14);
v_fieldInst_x3f_2788_ = lean_ctor_get(v_v_2772_, 15);
v_charInst_x3f_2789_ = lean_ctor_get(v_v_2772_, 16);
v_zero_2790_ = lean_ctor_get(v_v_2772_, 17);
v_ofNatZero_2791_ = lean_ctor_get(v_v_2772_, 18);
v_one_x3f_2792_ = lean_ctor_get(v_v_2772_, 19);
v_leFn_x3f_2793_ = lean_ctor_get(v_v_2772_, 20);
v_ltFn_x3f_2794_ = lean_ctor_get(v_v_2772_, 21);
v_addFn_2795_ = lean_ctor_get(v_v_2772_, 22);
v_zsmulFn_2796_ = lean_ctor_get(v_v_2772_, 23);
v_nsmulFn_2797_ = lean_ctor_get(v_v_2772_, 24);
v_zsmulFn_x3f_2798_ = lean_ctor_get(v_v_2772_, 25);
v_nsmulFn_x3f_2799_ = lean_ctor_get(v_v_2772_, 26);
v_homomulFn_x3f_2800_ = lean_ctor_get(v_v_2772_, 27);
v_subFn_2801_ = lean_ctor_get(v_v_2772_, 28);
v_negFn_2802_ = lean_ctor_get(v_v_2772_, 29);
v_vars_2803_ = lean_ctor_get(v_v_2772_, 30);
v_varMap_2804_ = lean_ctor_get(v_v_2772_, 31);
v_lowers_2805_ = lean_ctor_get(v_v_2772_, 32);
v_uppers_2806_ = lean_ctor_get(v_v_2772_, 33);
v_diseqs_2807_ = lean_ctor_get(v_v_2772_, 34);
v_assignment_2808_ = lean_ctor_get(v_v_2772_, 35);
v_caseSplits_2809_ = lean_ctor_get_uint8(v_v_2772_, sizeof(void*)*42);
v_conflict_x3f_2810_ = lean_ctor_get(v_v_2772_, 36);
v_diseqSplits_2811_ = lean_ctor_get(v_v_2772_, 37);
v_elimEqs_2812_ = lean_ctor_get(v_v_2772_, 38);
v_elimStack_2813_ = lean_ctor_get(v_v_2772_, 39);
v_occurs_2814_ = lean_ctor_get(v_v_2772_, 40);
v_ignored_2815_ = lean_ctor_get(v_v_2772_, 41);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_v_2772_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2817_ = v_v_2772_;
v_isShared_2818_ = v_isSharedCheck_2829_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_ignored_2815_);
lean_inc(v_occurs_2814_);
lean_inc(v_elimStack_2813_);
lean_inc(v_elimEqs_2812_);
lean_inc(v_diseqSplits_2811_);
lean_inc(v_conflict_x3f_2810_);
lean_inc(v_assignment_2808_);
lean_inc(v_diseqs_2807_);
lean_inc(v_uppers_2806_);
lean_inc(v_lowers_2805_);
lean_inc(v_varMap_2804_);
lean_inc(v_vars_2803_);
lean_inc(v_negFn_2802_);
lean_inc(v_subFn_2801_);
lean_inc(v_homomulFn_x3f_2800_);
lean_inc(v_nsmulFn_x3f_2799_);
lean_inc(v_zsmulFn_x3f_2798_);
lean_inc(v_nsmulFn_2797_);
lean_inc(v_zsmulFn_2796_);
lean_inc(v_addFn_2795_);
lean_inc(v_ltFn_x3f_2794_);
lean_inc(v_leFn_x3f_2793_);
lean_inc(v_one_x3f_2792_);
lean_inc(v_ofNatZero_2791_);
lean_inc(v_zero_2790_);
lean_inc(v_charInst_x3f_2789_);
lean_inc(v_fieldInst_x3f_2788_);
lean_inc(v_orderedRingInst_x3f_2787_);
lean_inc(v_commRingInst_x3f_2786_);
lean_inc(v_ringInst_x3f_2785_);
lean_inc(v_noNatDivInst_x3f_2784_);
lean_inc(v_isLinearInst_x3f_2783_);
lean_inc(v_orderedAddInst_x3f_2782_);
lean_inc(v_isPreorderInst_x3f_2781_);
lean_inc(v_lawfulOrderLTInst_x3f_2780_);
lean_inc(v_ltInst_x3f_2779_);
lean_inc(v_leInst_x3f_2778_);
lean_inc(v_intModuleInst_2777_);
lean_inc(v_u_2776_);
lean_inc(v_type_2775_);
lean_inc(v_ringId_x3f_2774_);
lean_inc(v_id_2773_);
lean_dec(v_v_2772_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2829_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_xs_x27_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2819_ = lean_box(0);
v_xs_x27_2820_ = lean_array_fset(v_structs_2759_, v___y_2756_, v___x_2819_);
v___x_2821_ = l_Lean_PersistentArray_push___redArg(v_ignored_2815_, v_a_2757_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 41, v___x_2821_);
v___x_2823_ = v___x_2817_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_id_2773_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_ringId_x3f_2774_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_type_2775_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_u_2776_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_intModuleInst_2777_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_leInst_x3f_2778_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_ltInst_x3f_2779_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_lawfulOrderLTInst_x3f_2780_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_isPreorderInst_x3f_2781_);
lean_ctor_set(v_reuseFailAlloc_2828_, 9, v_orderedAddInst_x3f_2782_);
lean_ctor_set(v_reuseFailAlloc_2828_, 10, v_isLinearInst_x3f_2783_);
lean_ctor_set(v_reuseFailAlloc_2828_, 11, v_noNatDivInst_x3f_2784_);
lean_ctor_set(v_reuseFailAlloc_2828_, 12, v_ringInst_x3f_2785_);
lean_ctor_set(v_reuseFailAlloc_2828_, 13, v_commRingInst_x3f_2786_);
lean_ctor_set(v_reuseFailAlloc_2828_, 14, v_orderedRingInst_x3f_2787_);
lean_ctor_set(v_reuseFailAlloc_2828_, 15, v_fieldInst_x3f_2788_);
lean_ctor_set(v_reuseFailAlloc_2828_, 16, v_charInst_x3f_2789_);
lean_ctor_set(v_reuseFailAlloc_2828_, 17, v_zero_2790_);
lean_ctor_set(v_reuseFailAlloc_2828_, 18, v_ofNatZero_2791_);
lean_ctor_set(v_reuseFailAlloc_2828_, 19, v_one_x3f_2792_);
lean_ctor_set(v_reuseFailAlloc_2828_, 20, v_leFn_x3f_2793_);
lean_ctor_set(v_reuseFailAlloc_2828_, 21, v_ltFn_x3f_2794_);
lean_ctor_set(v_reuseFailAlloc_2828_, 22, v_addFn_2795_);
lean_ctor_set(v_reuseFailAlloc_2828_, 23, v_zsmulFn_2796_);
lean_ctor_set(v_reuseFailAlloc_2828_, 24, v_nsmulFn_2797_);
lean_ctor_set(v_reuseFailAlloc_2828_, 25, v_zsmulFn_x3f_2798_);
lean_ctor_set(v_reuseFailAlloc_2828_, 26, v_nsmulFn_x3f_2799_);
lean_ctor_set(v_reuseFailAlloc_2828_, 27, v_homomulFn_x3f_2800_);
lean_ctor_set(v_reuseFailAlloc_2828_, 28, v_subFn_2801_);
lean_ctor_set(v_reuseFailAlloc_2828_, 29, v_negFn_2802_);
lean_ctor_set(v_reuseFailAlloc_2828_, 30, v_vars_2803_);
lean_ctor_set(v_reuseFailAlloc_2828_, 31, v_varMap_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 32, v_lowers_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 33, v_uppers_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 34, v_diseqs_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 35, v_assignment_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 36, v_conflict_x3f_2810_);
lean_ctor_set(v_reuseFailAlloc_2828_, 37, v_diseqSplits_2811_);
lean_ctor_set(v_reuseFailAlloc_2828_, 38, v_elimEqs_2812_);
lean_ctor_set(v_reuseFailAlloc_2828_, 39, v_elimStack_2813_);
lean_ctor_set(v_reuseFailAlloc_2828_, 40, v_occurs_2814_);
lean_ctor_set(v_reuseFailAlloc_2828_, 41, v___x_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*42, v_caseSplits_2809_);
v___x_2823_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = lean_array_fset(v_xs_x27_2820_, v___y_2756_, v___x_2823_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2824_);
v___x_2826_ = v___x_2770_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_typeIdOf_2760_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_exprToStructId_2761_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_exprToStructIdEntries_2762_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_forbiddenNatModules_2763_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v_natStructs_2764_);
lean_ctor_set(v_reuseFailAlloc_2827_, 6, v_natTypeIdOf_2765_);
lean_ctor_set(v_reuseFailAlloc_2827_, 7, v_exprToNatStructId_2766_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2839_, lean_object* v_a_2840_, lean_object* v_s_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2839_, v_a_2840_, v_s_2841_);
lean_dec(v___y_2839_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v_cls_2888_; lean_object* v___x_2889_; lean_object* v_a_2890_; uint8_t v___x_2891_; 
v_cls_2888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2889_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_2888_, v_a_2860_);
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = lean_unbox(v_a_2890_);
lean_dec(v_a_2890_);
if (v___x_2891_ == 0)
{
v___y_2864_ = v_a_2851_;
v___y_2865_ = v_a_2852_;
v___y_2866_ = v_a_2853_;
v___y_2867_ = v_a_2854_;
v___y_2868_ = v_a_2855_;
v___y_2869_ = v_a_2856_;
v___y_2870_ = v_a_2857_;
v___y_2871_ = v_a_2858_;
v___y_2872_ = v_a_2859_;
v___y_2873_ = v_a_2860_;
v___y_2874_ = v_a_2861_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofExpr(v_a_2893_);
v___x_2895_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_2888_, v___x_2894_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_dec_ref(v___x_2895_);
v___y_2864_ = v_a_2851_;
v___y_2865_ = v_a_2852_;
v___y_2866_ = v_a_2853_;
v___y_2867_ = v_a_2854_;
v___y_2868_ = v_a_2855_;
v___y_2869_ = v_a_2856_;
v___y_2870_ = v_a_2857_;
v___y_2871_ = v_a_2858_;
v___y_2872_ = v_a_2859_;
v___y_2873_ = v_a_2860_;
v___y_2874_ = v_a_2861_;
goto v___jp_2863_;
}
else
{
lean_dec(v_a_2851_);
return v___x_2895_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_a_2851_);
v_a_2896_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2892_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2892_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v___jp_2863_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2850_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___f_2877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2877_, 0, v___y_2864_);
lean_closure_set(v___f_2877_, 1, v_a_2876_);
v___x_2878_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2879_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2878_, v___f_2877_, v___y_2865_);
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v___y_2864_);
v_a_2880_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2875_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2875_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_c_2904_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_fileName_2931_; lean_object* v_fileMap_2932_; lean_object* v_options_2933_; lean_object* v_currRecDepth_2934_; lean_object* v_maxRecDepth_2935_; lean_object* v_ref_2936_; lean_object* v_currNamespace_2937_; lean_object* v_openDecls_2938_; lean_object* v_initHeartbeats_2939_; lean_object* v_maxHeartbeats_2940_; lean_object* v_quotContext_2941_; lean_object* v_currMacroScope_2942_; uint8_t v_diag_2943_; lean_object* v_cancelTk_x3f_2944_; uint8_t v_suppressElabErrors_2945_; lean_object* v_inheritedTraceOptions_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3005_; 
v_fileName_2931_ = lean_ctor_get(v_a_2928_, 0);
v_fileMap_2932_ = lean_ctor_get(v_a_2928_, 1);
v_options_2933_ = lean_ctor_get(v_a_2928_, 2);
v_currRecDepth_2934_ = lean_ctor_get(v_a_2928_, 3);
v_maxRecDepth_2935_ = lean_ctor_get(v_a_2928_, 4);
v_ref_2936_ = lean_ctor_get(v_a_2928_, 5);
v_currNamespace_2937_ = lean_ctor_get(v_a_2928_, 6);
v_openDecls_2938_ = lean_ctor_get(v_a_2928_, 7);
v_initHeartbeats_2939_ = lean_ctor_get(v_a_2928_, 8);
v_maxHeartbeats_2940_ = lean_ctor_get(v_a_2928_, 9);
v_quotContext_2941_ = lean_ctor_get(v_a_2928_, 10);
v_currMacroScope_2942_ = lean_ctor_get(v_a_2928_, 11);
v_diag_2943_ = lean_ctor_get_uint8(v_a_2928_, sizeof(void*)*14);
v_cancelTk_x3f_2944_ = lean_ctor_get(v_a_2928_, 12);
v_suppressElabErrors_2945_ = lean_ctor_get_uint8(v_a_2928_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2946_ = lean_ctor_get(v_a_2928_, 13);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_a_2928_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2948_ = v_a_2928_;
v_isShared_2949_ = v_isSharedCheck_3005_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_inheritedTraceOptions_2946_);
lean_inc(v_cancelTk_x3f_2944_);
lean_inc(v_currMacroScope_2942_);
lean_inc(v_quotContext_2941_);
lean_inc(v_maxHeartbeats_2940_);
lean_inc(v_initHeartbeats_2939_);
lean_inc(v_openDecls_2938_);
lean_inc(v_currNamespace_2937_);
lean_inc(v_ref_2936_);
lean_inc(v_maxRecDepth_2935_);
lean_inc(v_currRecDepth_2934_);
lean_inc(v_options_2933_);
lean_inc(v_fileMap_2932_);
lean_inc(v_fileName_2931_);
lean_dec(v_a_2928_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3005_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_nat_dec_eq(v_currRecDepth_2934_, v_maxRecDepth_2935_);
if (v___x_2950_ == 0)
{
lean_object* v_p_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v_p_2951_ = lean_ctor_get(v_c_u2082_2918_, 0);
v___x_2952_ = lean_unsigned_to_nat(1u);
v___x_2953_ = lean_nat_add(v_currRecDepth_2934_, v___x_2952_);
lean_dec(v_currRecDepth_2934_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 3, v___x_2953_);
v___x_2955_ = v___x_2948_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_fileName_2931_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_fileMap_2932_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_options_2933_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_maxRecDepth_2935_);
lean_ctor_set(v_reuseFailAlloc_3003_, 5, v_ref_2936_);
lean_ctor_set(v_reuseFailAlloc_3003_, 6, v_currNamespace_2937_);
lean_ctor_set(v_reuseFailAlloc_3003_, 7, v_openDecls_2938_);
lean_ctor_set(v_reuseFailAlloc_3003_, 8, v_initHeartbeats_2939_);
lean_ctor_set(v_reuseFailAlloc_3003_, 9, v_maxHeartbeats_2940_);
lean_ctor_set(v_reuseFailAlloc_3003_, 10, v_quotContext_2941_);
lean_ctor_set(v_reuseFailAlloc_3003_, 11, v_currMacroScope_2942_);
lean_ctor_set(v_reuseFailAlloc_3003_, 12, v_cancelTk_x3f_2944_);
lean_ctor_set(v_reuseFailAlloc_3003_, 13, v_inheritedTraceOptions_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*14, v_diag_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*14 + 1, v_suppressElabErrors_2945_);
v___x_2955_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2951_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v___x_2955_, v_a_2929_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2994_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2994_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2994_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
if (lean_obj_tag(v_a_2957_) == 1)
{
lean_object* v_val_2961_; lean_object* v_snd_2962_; lean_object* v_snd_2963_; lean_object* v_fst_2964_; lean_object* v_fst_2965_; lean_object* v_p_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_del_object(v___x_2959_);
v_val_2961_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_val_2961_);
lean_dec_ref(v_a_2957_);
v_snd_2962_ = lean_ctor_get(v_val_2961_, 1);
lean_inc(v_snd_2962_);
v_snd_2963_ = lean_ctor_get(v_snd_2962_, 1);
lean_inc(v_snd_2963_);
v_fst_2964_ = lean_ctor_get(v_val_2961_, 0);
lean_inc(v_fst_2964_);
lean_dec(v_val_2961_);
v_fst_2965_ = lean_ctor_get(v_snd_2962_, 0);
lean_inc(v_fst_2965_);
lean_dec(v_snd_2962_);
v_p_2966_ = lean_ctor_get(v_snd_2963_, 0);
v___x_2967_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2966_, v_fst_2965_);
lean_inc_ref(v_c_u2082_2918_);
v___x_2968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2967_, v_fst_2965_, v_snd_2963_, v_fst_2964_, v_c_u2082_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v___x_2955_, v_a_2929_);
lean_dec(v_fst_2965_);
lean_dec(v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2968_);
if (lean_obj_tag(v_a_2969_) == 1)
{
lean_object* v_val_2970_; 
lean_dec_ref(v_c_u2082_2918_);
v_val_2970_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_val_2970_);
lean_dec_ref(v_a_2969_);
v_c_u2082_2918_ = v_val_2970_;
v_a_2928_ = v___x_2955_;
goto _start;
}
else
{
lean_object* v___x_2972_; 
lean_dec(v_a_2969_);
v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v___x_2955_, v_a_2929_);
lean_dec_ref(v___x_2955_);
lean_dec_ref(v_c_u2082_2918_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v___x_2972_, 0);
lean_dec(v_unused_2981_);
v___x_2974_ = v___x_2972_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_dec(v___x_2972_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_box(0);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2982_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2972_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2972_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2955_);
lean_dec(v_a_2919_);
lean_dec_ref(v_c_u2082_2918_);
return v___x_2968_;
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_dec(v_a_2957_);
lean_dec_ref(v___x_2955_);
lean_dec(v_a_2919_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_c_u2082_2918_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2990_);
v___x_2992_ = v___x_2959_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v___x_2955_);
lean_dec(v_a_2919_);
lean_dec_ref(v_c_u2082_2918_);
v_a_2995_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2956_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2956_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
else
{
lean_object* v___x_3004_; 
lean_del_object(v___x_2948_);
lean_dec_ref(v_inheritedTraceOptions_2946_);
lean_dec(v_cancelTk_x3f_2944_);
lean_dec(v_currMacroScope_2942_);
lean_dec(v_quotContext_2941_);
lean_dec(v_maxHeartbeats_2940_);
lean_dec(v_initHeartbeats_2939_);
lean_dec(v_openDecls_2938_);
lean_dec(v_currNamespace_2937_);
lean_dec(v_maxRecDepth_2935_);
lean_dec(v_currRecDepth_2934_);
lean_dec_ref(v_options_2933_);
lean_dec_ref(v_fileMap_2932_);
lean_dec_ref(v_fileName_2931_);
lean_dec(v_a_2919_);
lean_dec_ref(v_c_u2082_2918_);
v___x_3004_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2936_);
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec(v_a_3008_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object* v_val_3020_, lean_object* v_x_3021_, size_t v_x_3022_, size_t v_x_3023_){
_start:
{
if (lean_obj_tag(v_x_3021_) == 0)
{
lean_object* v_cs_3024_; size_t v_j_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_cs_3024_ = lean_ctor_get(v_x_3021_, 0);
v_j_3025_ = lean_usize_shift_right(v_x_3022_, v_x_3023_);
v___x_3026_ = lean_usize_to_nat(v_j_3025_);
v___x_3027_ = lean_array_get_size(v_cs_3024_);
v___x_3028_ = lean_nat_dec_lt(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v___x_3026_);
lean_dec_ref(v_val_3020_);
return v_x_3021_;
}
else
{
lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3046_; 
lean_inc_ref(v_cs_3024_);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v_x_3021_, 0);
lean_dec(v_unused_3047_);
v___x_3030_ = v_x_3021_;
v_isShared_3031_ = v_isSharedCheck_3046_;
goto v_resetjp_3029_;
}
else
{
lean_dec(v_x_3021_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3046_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
size_t v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; size_t v_i_3035_; size_t v___x_3036_; size_t v_shift_3037_; lean_object* v_v_3038_; lean_object* v___x_3039_; lean_object* v_xs_x27_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_shift_left(v___x_3032_, v_x_3023_);
v___x_3034_ = lean_usize_sub(v___x_3033_, v___x_3032_);
v_i_3035_ = lean_usize_land(v_x_3022_, v___x_3034_);
v___x_3036_ = ((size_t)5ULL);
v_shift_3037_ = lean_usize_sub(v_x_3023_, v___x_3036_);
v_v_3038_ = lean_array_fget(v_cs_3024_, v___x_3026_);
v___x_3039_ = lean_box(0);
v_xs_x27_3040_ = lean_array_fset(v_cs_3024_, v___x_3026_, v___x_3039_);
v___x_3041_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3020_, v_v_3038_, v_i_3035_, v_shift_3037_);
v___x_3042_ = lean_array_fset(v_xs_x27_3040_, v___x_3026_, v___x_3041_);
lean_dec(v___x_3026_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3042_);
v___x_3044_ = v___x_3030_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_vs_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_vs_3048_ = lean_ctor_get(v_x_3021_, 0);
v___x_3049_ = lean_usize_to_nat(v_x_3022_);
v___x_3050_ = lean_array_get_size(v_vs_3048_);
v___x_3051_ = lean_nat_dec_lt(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_dec(v___x_3049_);
lean_dec_ref(v_val_3020_);
return v_x_3021_;
}
else
{
lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3063_; 
lean_inc_ref(v_vs_3048_);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v_x_3021_, 0);
lean_dec(v_unused_3064_);
v___x_3053_ = v_x_3021_;
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v_x_3021_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_v_3055_; lean_object* v___x_3056_; lean_object* v_xs_x27_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v_v_3055_ = lean_array_fget(v_vs_3048_, v___x_3049_);
v___x_3056_ = lean_box(0);
v_xs_x27_3057_ = lean_array_fset(v_vs_3048_, v___x_3049_, v___x_3056_);
v___x_3058_ = l_Lean_PersistentArray_push___redArg(v_v_3055_, v_val_3020_);
v___x_3059_ = lean_array_fset(v_xs_x27_3057_, v___x_3049_, v___x_3058_);
lean_dec(v___x_3049_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3059_);
v___x_3061_ = v___x_3053_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object* v_val_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_, lean_object* v_x_3068_){
_start:
{
size_t v_x_38838__boxed_3069_; size_t v_x_38839__boxed_3070_; lean_object* v_res_3071_; 
v_x_38838__boxed_3069_ = lean_unbox_usize(v_x_3067_);
lean_dec(v_x_3067_);
v_x_38839__boxed_3070_ = lean_unbox_usize(v_x_3068_);
lean_dec(v_x_3068_);
v_res_3071_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3065_, v_x_3066_, v_x_38838__boxed_3069_, v_x_38839__boxed_3070_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_3072_, lean_object* v_inst_3073_, lean_object* v_t_3074_, lean_object* v_i_3075_){
_start:
{
lean_object* v_root_3076_; lean_object* v_tail_3077_; lean_object* v_size_3078_; size_t v_shift_3079_; lean_object* v_tailOff_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3104_; 
v_root_3076_ = lean_ctor_get(v_t_3074_, 0);
v_tail_3077_ = lean_ctor_get(v_t_3074_, 1);
v_size_3078_ = lean_ctor_get(v_t_3074_, 2);
v_shift_3079_ = lean_ctor_get_usize(v_t_3074_, 4);
v_tailOff_3080_ = lean_ctor_get(v_t_3074_, 3);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_t_3074_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3082_ = v_t_3074_;
v_isShared_3083_ = v_isSharedCheck_3104_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_tailOff_3080_);
lean_inc(v_size_3078_);
lean_inc(v_tail_3077_);
lean_inc(v_root_3076_);
lean_dec(v_t_3074_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3104_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_nat_dec_le(v_tailOff_3080_, v_i_3075_);
if (v___x_3084_ == 0)
{
size_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3085_ = lean_usize_of_nat(v_i_3075_);
v___x_3086_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3072_, v_root_3076_, v___x_3085_, v_shift_3079_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3086_);
v___x_3088_ = v___x_3082_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_tail_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_size_3078_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_tailOff_3080_);
lean_ctor_set_usize(v_reuseFailAlloc_3089_, 4, v_shift_3079_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = lean_nat_sub(v_i_3075_, v_tailOff_3080_);
v___x_3091_ = lean_array_get_size(v_tail_3077_);
v___x_3092_ = lean_nat_dec_lt(v___x_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3094_; 
lean_dec(v___x_3090_);
lean_dec_ref(v_val_3072_);
if (v_isShared_3083_ == 0)
{
v___x_3094_ = v___x_3082_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_root_3076_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_tail_3077_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_size_3078_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_tailOff_3080_);
lean_ctor_set_usize(v_reuseFailAlloc_3095_, 4, v_shift_3079_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
else
{
lean_object* v_v_3096_; lean_object* v___x_3097_; lean_object* v_xs_x27_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v_v_3096_ = lean_array_fget(v_tail_3077_, v___x_3090_);
v___x_3097_ = lean_box(0);
v_xs_x27_3098_ = lean_array_fset(v_tail_3077_, v___x_3090_, v___x_3097_);
v___x_3099_ = l_Lean_PersistentArray_push___redArg(v_v_3096_, v_val_3072_);
v___x_3100_ = lean_array_fset(v_xs_x27_3098_, v___x_3090_, v___x_3099_);
lean_dec(v___x_3090_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3100_);
v___x_3102_ = v___x_3082_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_root_3076_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_size_3078_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_tailOff_3080_);
lean_ctor_set_usize(v_reuseFailAlloc_3103_, 4, v_shift_3079_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3105_, lean_object* v_inst_3106_, lean_object* v_t_3107_, lean_object* v_i_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3105_, v_inst_3106_, v_t_3107_, v_i_3108_);
lean_dec(v_i_3108_);
lean_dec_ref(v_inst_3106_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3110_, lean_object* v_val_3111_, lean_object* v___x_3112_, lean_object* v_v_3113_, lean_object* v_s_3114_){
_start:
{
lean_object* v_structs_3115_; lean_object* v_typeIdOf_3116_; lean_object* v_exprToStructId_3117_; lean_object* v_exprToStructIdEntries_3118_; lean_object* v_forbiddenNatModules_3119_; lean_object* v_natStructs_3120_; lean_object* v_natTypeIdOf_3121_; lean_object* v_exprToNatStructId_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_structs_3115_ = lean_ctor_get(v_s_3114_, 0);
v_typeIdOf_3116_ = lean_ctor_get(v_s_3114_, 1);
v_exprToStructId_3117_ = lean_ctor_get(v_s_3114_, 2);
v_exprToStructIdEntries_3118_ = lean_ctor_get(v_s_3114_, 3);
v_forbiddenNatModules_3119_ = lean_ctor_get(v_s_3114_, 4);
v_natStructs_3120_ = lean_ctor_get(v_s_3114_, 5);
v_natTypeIdOf_3121_ = lean_ctor_get(v_s_3114_, 6);
v_exprToNatStructId_3122_ = lean_ctor_get(v_s_3114_, 7);
v___x_3123_ = lean_array_get_size(v_structs_3115_);
v___x_3124_ = lean_nat_dec_lt(v___y_3110_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_dec_ref(v_val_3111_);
return v_s_3114_;
}
else
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3186_; 
lean_inc_ref(v_exprToNatStructId_3122_);
lean_inc_ref(v_natTypeIdOf_3121_);
lean_inc_ref(v_natStructs_3120_);
lean_inc_ref(v_forbiddenNatModules_3119_);
lean_inc_ref(v_exprToStructIdEntries_3118_);
lean_inc_ref(v_exprToStructId_3117_);
lean_inc_ref(v_typeIdOf_3116_);
lean_inc_ref(v_structs_3115_);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_s_3114_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; lean_object* v_unused_3190_; lean_object* v_unused_3191_; lean_object* v_unused_3192_; lean_object* v_unused_3193_; lean_object* v_unused_3194_; 
v_unused_3187_ = lean_ctor_get(v_s_3114_, 7);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_s_3114_, 6);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_s_3114_, 5);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v_s_3114_, 4);
lean_dec(v_unused_3190_);
v_unused_3191_ = lean_ctor_get(v_s_3114_, 3);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v_s_3114_, 2);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v_s_3114_, 1);
lean_dec(v_unused_3193_);
v_unused_3194_ = lean_ctor_get(v_s_3114_, 0);
lean_dec(v_unused_3194_);
v___x_3126_ = v_s_3114_;
v_isShared_3127_ = v_isSharedCheck_3186_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_s_3114_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3186_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_v_3128_; lean_object* v_id_3129_; lean_object* v_ringId_x3f_3130_; lean_object* v_type_3131_; lean_object* v_u_3132_; lean_object* v_intModuleInst_3133_; lean_object* v_leInst_x3f_3134_; lean_object* v_ltInst_x3f_3135_; lean_object* v_lawfulOrderLTInst_x3f_3136_; lean_object* v_isPreorderInst_x3f_3137_; lean_object* v_orderedAddInst_x3f_3138_; lean_object* v_isLinearInst_x3f_3139_; lean_object* v_noNatDivInst_x3f_3140_; lean_object* v_ringInst_x3f_3141_; lean_object* v_commRingInst_x3f_3142_; lean_object* v_orderedRingInst_x3f_3143_; lean_object* v_fieldInst_x3f_3144_; lean_object* v_charInst_x3f_3145_; lean_object* v_zero_3146_; lean_object* v_ofNatZero_3147_; lean_object* v_one_x3f_3148_; lean_object* v_leFn_x3f_3149_; lean_object* v_ltFn_x3f_3150_; lean_object* v_addFn_3151_; lean_object* v_zsmulFn_3152_; lean_object* v_nsmulFn_3153_; lean_object* v_zsmulFn_x3f_3154_; lean_object* v_nsmulFn_x3f_3155_; lean_object* v_homomulFn_x3f_3156_; lean_object* v_subFn_3157_; lean_object* v_negFn_3158_; lean_object* v_vars_3159_; lean_object* v_varMap_3160_; lean_object* v_lowers_3161_; lean_object* v_uppers_3162_; lean_object* v_diseqs_3163_; lean_object* v_assignment_3164_; uint8_t v_caseSplits_3165_; lean_object* v_conflict_x3f_3166_; lean_object* v_diseqSplits_3167_; lean_object* v_elimEqs_3168_; lean_object* v_elimStack_3169_; lean_object* v_occurs_3170_; lean_object* v_ignored_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3185_; 
v_v_3128_ = lean_array_fget(v_structs_3115_, v___y_3110_);
v_id_3129_ = lean_ctor_get(v_v_3128_, 0);
v_ringId_x3f_3130_ = lean_ctor_get(v_v_3128_, 1);
v_type_3131_ = lean_ctor_get(v_v_3128_, 2);
v_u_3132_ = lean_ctor_get(v_v_3128_, 3);
v_intModuleInst_3133_ = lean_ctor_get(v_v_3128_, 4);
v_leInst_x3f_3134_ = lean_ctor_get(v_v_3128_, 5);
v_ltInst_x3f_3135_ = lean_ctor_get(v_v_3128_, 6);
v_lawfulOrderLTInst_x3f_3136_ = lean_ctor_get(v_v_3128_, 7);
v_isPreorderInst_x3f_3137_ = lean_ctor_get(v_v_3128_, 8);
v_orderedAddInst_x3f_3138_ = lean_ctor_get(v_v_3128_, 9);
v_isLinearInst_x3f_3139_ = lean_ctor_get(v_v_3128_, 10);
v_noNatDivInst_x3f_3140_ = lean_ctor_get(v_v_3128_, 11);
v_ringInst_x3f_3141_ = lean_ctor_get(v_v_3128_, 12);
v_commRingInst_x3f_3142_ = lean_ctor_get(v_v_3128_, 13);
v_orderedRingInst_x3f_3143_ = lean_ctor_get(v_v_3128_, 14);
v_fieldInst_x3f_3144_ = lean_ctor_get(v_v_3128_, 15);
v_charInst_x3f_3145_ = lean_ctor_get(v_v_3128_, 16);
v_zero_3146_ = lean_ctor_get(v_v_3128_, 17);
v_ofNatZero_3147_ = lean_ctor_get(v_v_3128_, 18);
v_one_x3f_3148_ = lean_ctor_get(v_v_3128_, 19);
v_leFn_x3f_3149_ = lean_ctor_get(v_v_3128_, 20);
v_ltFn_x3f_3150_ = lean_ctor_get(v_v_3128_, 21);
v_addFn_3151_ = lean_ctor_get(v_v_3128_, 22);
v_zsmulFn_3152_ = lean_ctor_get(v_v_3128_, 23);
v_nsmulFn_3153_ = lean_ctor_get(v_v_3128_, 24);
v_zsmulFn_x3f_3154_ = lean_ctor_get(v_v_3128_, 25);
v_nsmulFn_x3f_3155_ = lean_ctor_get(v_v_3128_, 26);
v_homomulFn_x3f_3156_ = lean_ctor_get(v_v_3128_, 27);
v_subFn_3157_ = lean_ctor_get(v_v_3128_, 28);
v_negFn_3158_ = lean_ctor_get(v_v_3128_, 29);
v_vars_3159_ = lean_ctor_get(v_v_3128_, 30);
v_varMap_3160_ = lean_ctor_get(v_v_3128_, 31);
v_lowers_3161_ = lean_ctor_get(v_v_3128_, 32);
v_uppers_3162_ = lean_ctor_get(v_v_3128_, 33);
v_diseqs_3163_ = lean_ctor_get(v_v_3128_, 34);
v_assignment_3164_ = lean_ctor_get(v_v_3128_, 35);
v_caseSplits_3165_ = lean_ctor_get_uint8(v_v_3128_, sizeof(void*)*42);
v_conflict_x3f_3166_ = lean_ctor_get(v_v_3128_, 36);
v_diseqSplits_3167_ = lean_ctor_get(v_v_3128_, 37);
v_elimEqs_3168_ = lean_ctor_get(v_v_3128_, 38);
v_elimStack_3169_ = lean_ctor_get(v_v_3128_, 39);
v_occurs_3170_ = lean_ctor_get(v_v_3128_, 40);
v_ignored_3171_ = lean_ctor_get(v_v_3128_, 41);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_v_3128_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3173_ = v_v_3128_;
v_isShared_3174_ = v_isSharedCheck_3185_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_ignored_3171_);
lean_inc(v_occurs_3170_);
lean_inc(v_elimStack_3169_);
lean_inc(v_elimEqs_3168_);
lean_inc(v_diseqSplits_3167_);
lean_inc(v_conflict_x3f_3166_);
lean_inc(v_assignment_3164_);
lean_inc(v_diseqs_3163_);
lean_inc(v_uppers_3162_);
lean_inc(v_lowers_3161_);
lean_inc(v_varMap_3160_);
lean_inc(v_vars_3159_);
lean_inc(v_negFn_3158_);
lean_inc(v_subFn_3157_);
lean_inc(v_homomulFn_x3f_3156_);
lean_inc(v_nsmulFn_x3f_3155_);
lean_inc(v_zsmulFn_x3f_3154_);
lean_inc(v_nsmulFn_3153_);
lean_inc(v_zsmulFn_3152_);
lean_inc(v_addFn_3151_);
lean_inc(v_ltFn_x3f_3150_);
lean_inc(v_leFn_x3f_3149_);
lean_inc(v_one_x3f_3148_);
lean_inc(v_ofNatZero_3147_);
lean_inc(v_zero_3146_);
lean_inc(v_charInst_x3f_3145_);
lean_inc(v_fieldInst_x3f_3144_);
lean_inc(v_orderedRingInst_x3f_3143_);
lean_inc(v_commRingInst_x3f_3142_);
lean_inc(v_ringInst_x3f_3141_);
lean_inc(v_noNatDivInst_x3f_3140_);
lean_inc(v_isLinearInst_x3f_3139_);
lean_inc(v_orderedAddInst_x3f_3138_);
lean_inc(v_isPreorderInst_x3f_3137_);
lean_inc(v_lawfulOrderLTInst_x3f_3136_);
lean_inc(v_ltInst_x3f_3135_);
lean_inc(v_leInst_x3f_3134_);
lean_inc(v_intModuleInst_3133_);
lean_inc(v_u_3132_);
lean_inc(v_type_3131_);
lean_inc(v_ringId_x3f_3130_);
lean_inc(v_id_3129_);
lean_dec(v_v_3128_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3185_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v_xs_x27_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3175_ = lean_box(0);
v_xs_x27_3176_ = lean_array_fset(v_structs_3115_, v___y_3110_, v___x_3175_);
v___x_3177_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3111_, v___x_3112_, v_diseqs_3163_, v_v_3113_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 34, v___x_3177_);
v___x_3179_ = v___x_3173_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_id_3129_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_ringId_x3f_3130_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_type_3131_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_u_3132_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_intModuleInst_3133_);
lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_leInst_x3f_3134_);
lean_ctor_set(v_reuseFailAlloc_3184_, 6, v_ltInst_x3f_3135_);
lean_ctor_set(v_reuseFailAlloc_3184_, 7, v_lawfulOrderLTInst_x3f_3136_);
lean_ctor_set(v_reuseFailAlloc_3184_, 8, v_isPreorderInst_x3f_3137_);
lean_ctor_set(v_reuseFailAlloc_3184_, 9, v_orderedAddInst_x3f_3138_);
lean_ctor_set(v_reuseFailAlloc_3184_, 10, v_isLinearInst_x3f_3139_);
lean_ctor_set(v_reuseFailAlloc_3184_, 11, v_noNatDivInst_x3f_3140_);
lean_ctor_set(v_reuseFailAlloc_3184_, 12, v_ringInst_x3f_3141_);
lean_ctor_set(v_reuseFailAlloc_3184_, 13, v_commRingInst_x3f_3142_);
lean_ctor_set(v_reuseFailAlloc_3184_, 14, v_orderedRingInst_x3f_3143_);
lean_ctor_set(v_reuseFailAlloc_3184_, 15, v_fieldInst_x3f_3144_);
lean_ctor_set(v_reuseFailAlloc_3184_, 16, v_charInst_x3f_3145_);
lean_ctor_set(v_reuseFailAlloc_3184_, 17, v_zero_3146_);
lean_ctor_set(v_reuseFailAlloc_3184_, 18, v_ofNatZero_3147_);
lean_ctor_set(v_reuseFailAlloc_3184_, 19, v_one_x3f_3148_);
lean_ctor_set(v_reuseFailAlloc_3184_, 20, v_leFn_x3f_3149_);
lean_ctor_set(v_reuseFailAlloc_3184_, 21, v_ltFn_x3f_3150_);
lean_ctor_set(v_reuseFailAlloc_3184_, 22, v_addFn_3151_);
lean_ctor_set(v_reuseFailAlloc_3184_, 23, v_zsmulFn_3152_);
lean_ctor_set(v_reuseFailAlloc_3184_, 24, v_nsmulFn_3153_);
lean_ctor_set(v_reuseFailAlloc_3184_, 25, v_zsmulFn_x3f_3154_);
lean_ctor_set(v_reuseFailAlloc_3184_, 26, v_nsmulFn_x3f_3155_);
lean_ctor_set(v_reuseFailAlloc_3184_, 27, v_homomulFn_x3f_3156_);
lean_ctor_set(v_reuseFailAlloc_3184_, 28, v_subFn_3157_);
lean_ctor_set(v_reuseFailAlloc_3184_, 29, v_negFn_3158_);
lean_ctor_set(v_reuseFailAlloc_3184_, 30, v_vars_3159_);
lean_ctor_set(v_reuseFailAlloc_3184_, 31, v_varMap_3160_);
lean_ctor_set(v_reuseFailAlloc_3184_, 32, v_lowers_3161_);
lean_ctor_set(v_reuseFailAlloc_3184_, 33, v_uppers_3162_);
lean_ctor_set(v_reuseFailAlloc_3184_, 34, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3184_, 35, v_assignment_3164_);
lean_ctor_set(v_reuseFailAlloc_3184_, 36, v_conflict_x3f_3166_);
lean_ctor_set(v_reuseFailAlloc_3184_, 37, v_diseqSplits_3167_);
lean_ctor_set(v_reuseFailAlloc_3184_, 38, v_elimEqs_3168_);
lean_ctor_set(v_reuseFailAlloc_3184_, 39, v_elimStack_3169_);
lean_ctor_set(v_reuseFailAlloc_3184_, 40, v_occurs_3170_);
lean_ctor_set(v_reuseFailAlloc_3184_, 41, v_ignored_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3184_, sizeof(void*)*42, v_caseSplits_3165_);
v___x_3179_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_array_fset(v_xs_x27_3176_, v___y_3110_, v___x_3179_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3180_);
v___x_3182_ = v___x_3126_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_typeIdOf_3116_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_exprToStructId_3117_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_exprToStructIdEntries_3118_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_forbiddenNatModules_3119_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_natStructs_3120_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_natTypeIdOf_3121_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_exprToNatStructId_3122_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3195_, lean_object* v_val_3196_, lean_object* v___x_3197_, lean_object* v_v_3198_, lean_object* v_s_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3195_, v_val_3196_, v___x_3197_, v_v_3198_, v_s_3199_);
lean_dec(v_v_3198_);
lean_dec_ref(v___x_3197_);
lean_dec(v___y_3195_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v_cls_3244_; lean_object* v___x_3245_; lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; uint8_t v___x_3356_; 
v_cls_3244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_3245_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_3244_, v_a_3226_);
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3356_ = lean_unbox(v_a_3246_);
lean_dec(v_a_3246_);
if (v___x_3356_ == 0)
{
v___y_3292_ = v_a_3217_;
v___y_3293_ = v_a_3218_;
v___y_3294_ = v_a_3219_;
v___y_3295_ = v_a_3220_;
v___y_3296_ = v_a_3221_;
v___y_3297_ = v_a_3222_;
v___y_3298_ = v_a_3223_;
v___y_3299_ = v_a_3224_;
v___y_3300_ = v_a_3225_;
v___y_3301_ = v_a_3226_;
v___y_3302_ = v_a_3227_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = l_Lean_MessageData_ofExpr(v_a_3358_);
v___x_3360_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_3244_, v___x_3359_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec_ref(v___x_3360_);
v___y_3292_ = v_a_3217_;
v___y_3293_ = v_a_3218_;
v___y_3294_ = v_a_3219_;
v___y_3295_ = v_a_3220_;
v___y_3296_ = v_a_3221_;
v___y_3297_ = v_a_3222_;
v___y_3298_ = v_a_3223_;
v___y_3299_ = v_a_3224_;
v___y_3300_ = v_a_3225_;
v___y_3301_ = v_a_3226_;
v___y_3302_ = v_a_3227_;
goto v___jp_3291_;
}
else
{
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_c_3216_);
return v___x_3360_;
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_c_3216_);
v_a_3361_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3357_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
v___jp_3229_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___y_3230_);
v___x_3243_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3242_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3243_;
}
v___jp_3248_:
{
lean_object* v___x_3265_; 
lean_inc(v___y_3254_);
v___x_3265_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3251_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v___f_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec_ref(v___x_3265_);
lean_inc(v___y_3254_);
v___f_3266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3266_, 0, v___y_3254_);
lean_closure_set(v___f_3266_, 1, v___y_3250_);
lean_closure_set(v___f_3266_, 2, v___x_3247_);
lean_closure_set(v___f_3266_, 3, v___y_3249_);
v___x_3267_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3268_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3267_, v___f_3266_, v___y_3255_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; 
lean_dec_ref(v___x_3268_);
v___x_3269_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3282_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
uint8_t v___x_3274_; uint8_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = 0;
v___x_3275_ = lean_unbox(v_a_3270_);
lean_dec(v_a_3270_);
v___x_3276_ = l_Lean_instBEqLBool_beq(v___x_3275_, v___x_3274_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v___y_3252_);
v___x_3277_ = lean_box(0);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3277_);
v___x_3279_ = v___x_3272_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
else
{
lean_object* v___x_3281_; 
lean_del_object(v___x_3272_);
v___x_3281_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3252_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
return v___x_3281_;
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v___y_3252_);
v_a_3283_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3269_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3269_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
return v___x_3268_;
}
}
else
{
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
return v___x_3265_;
}
}
v___jp_3291_:
{
lean_object* v___x_3303_; 
lean_inc_ref(v___y_3301_);
lean_inc(v___y_3292_);
v___x_3303_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3216_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3347_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3347_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3347_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
if (lean_obj_tag(v_a_3304_) == 1)
{
lean_object* v_val_3308_; lean_object* v_p_3309_; 
lean_del_object(v___x_3306_);
v_val_3308_ = lean_ctor_get(v_a_3304_, 0);
lean_inc(v_val_3308_);
lean_dec_ref(v_a_3304_);
v_p_3309_ = lean_ctor_get(v_val_3308_, 0);
if (lean_obj_tag(v_p_3309_) == 0)
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_a_3312_; uint8_t v___x_3313_; 
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2));
v___x_3311_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3310_, v___y_3301_);
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = lean_unbox(v_a_3312_);
lean_dec(v_a_3312_);
if (v___x_3313_ == 0)
{
v___y_3230_ = v_val_3308_;
v___y_3231_ = v___y_3292_;
v___y_3232_ = v___y_3293_;
v___y_3233_ = v___y_3294_;
v___y_3234_ = v___y_3295_;
v___y_3235_ = v___y_3296_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___y_3300_;
v___y_3240_ = v___y_3301_;
v___y_3241_ = v___y_3302_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3308_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = l_Lean_MessageData_ofExpr(v_a_3315_);
v___x_3317_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3310_, v___x_3316_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_dec_ref(v___x_3317_);
v___y_3230_ = v_val_3308_;
v___y_3231_ = v___y_3292_;
v___y_3232_ = v___y_3293_;
v___y_3233_ = v___y_3294_;
v___y_3234_ = v___y_3295_;
v___y_3235_ = v___y_3296_;
v___y_3236_ = v___y_3297_;
v___y_3237_ = v___y_3298_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___y_3300_;
v___y_3240_ = v___y_3301_;
v___y_3241_ = v___y_3302_;
goto v___jp_3229_;
}
else
{
lean_dec(v_val_3308_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
return v___x_3317_;
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_val_3308_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
v_a_3318_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3314_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3314_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
else
{
lean_object* v_v_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; uint8_t v___x_3330_; 
lean_inc_ref(v_p_3309_);
v_v_3326_ = lean_ctor_get(v_p_3309_, 1);
lean_inc(v_v_3326_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3328_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3327_, v___y_3301_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_unbox(v_a_3329_);
lean_dec(v_a_3329_);
if (v___x_3330_ == 0)
{
lean_inc(v_val_3308_);
lean_inc(v_v_3326_);
v___y_3249_ = v_v_3326_;
v___y_3250_ = v_val_3308_;
v___y_3251_ = v_p_3309_;
v___y_3252_ = v_v_3326_;
v___y_3253_ = v_val_3308_;
v___y_3254_ = v___y_3292_;
v___y_3255_ = v___y_3293_;
v___y_3256_ = v___y_3294_;
v___y_3257_ = v___y_3295_;
v___y_3258_ = v___y_3296_;
v___y_3259_ = v___y_3297_;
v___y_3260_ = v___y_3298_;
v___y_3261_ = v___y_3299_;
v___y_3262_ = v___y_3300_;
v___y_3263_ = v___y_3301_;
v___y_3264_ = v___y_3302_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3308_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = l_Lean_MessageData_ofExpr(v_a_3332_);
v___x_3334_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3327_, v___x_3333_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_dec_ref(v___x_3334_);
lean_inc(v_val_3308_);
lean_inc(v_v_3326_);
v___y_3249_ = v_v_3326_;
v___y_3250_ = v_val_3308_;
v___y_3251_ = v_p_3309_;
v___y_3252_ = v_v_3326_;
v___y_3253_ = v_val_3308_;
v___y_3254_ = v___y_3292_;
v___y_3255_ = v___y_3293_;
v___y_3256_ = v___y_3294_;
v___y_3257_ = v___y_3295_;
v___y_3258_ = v___y_3296_;
v___y_3259_ = v___y_3297_;
v___y_3260_ = v___y_3298_;
v___y_3261_ = v___y_3299_;
v___y_3262_ = v___y_3300_;
v___y_3263_ = v___y_3301_;
v___y_3264_ = v___y_3302_;
goto v___jp_3248_;
}
else
{
lean_dec_ref(v_p_3309_);
lean_dec(v_v_3326_);
lean_dec(v_val_3308_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
return v___x_3334_;
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_v_3326_);
lean_dec_ref(v_p_3309_);
lean_dec(v_val_3308_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
v_a_3335_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3331_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3331_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_dec(v_a_3304_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
v___x_3343_ = lean_box(0);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3343_);
v___x_3345_ = v___x_3306_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
v_a_3348_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3303_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3303_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_3383_, lean_object* v_inst_3384_, lean_object* v_x_3385_, size_t v_x_3386_, size_t v_x_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3383_, v_x_3385_, v_x_3386_, v_x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_3389_, lean_object* v_inst_3390_, lean_object* v_x_3391_, lean_object* v_x_3392_, lean_object* v_x_3393_){
_start:
{
size_t v_x_39415__boxed_3394_; size_t v_x_39416__boxed_3395_; lean_object* v_res_3396_; 
v_x_39415__boxed_3394_ = lean_unbox_usize(v_x_3392_);
lean_dec(v_x_3392_);
v_x_39416__boxed_3395_ = lean_unbox_usize(v_x_3393_);
lean_dec(v_x_3393_);
v_res_3396_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_3389_, v_inst_3390_, v_x_3391_, v_x_39415__boxed_3394_, v_x_39416__boxed_3395_);
lean_dec_ref(v_inst_3390_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3397_, lean_object* v_as_3398_, size_t v_sz_3399_, size_t v_i_3400_, lean_object* v_b_3401_){
_start:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_usize_dec_lt(v_i_3400_, v_sz_3399_);
if (v___x_3402_ == 0)
{
return v_b_3401_;
}
else
{
lean_object* v_snd_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3444_; 
v_snd_3403_ = lean_ctor_get(v_b_3401_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_b_3401_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_b_3401_, 0);
lean_dec(v_unused_3445_);
v___x_3405_ = v_b_3401_;
v_isShared_3406_ = v_isSharedCheck_3444_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_snd_3403_);
lean_dec(v_b_3401_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3444_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_fst_3407_; lean_object* v_snd_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3443_; 
v_fst_3407_ = lean_ctor_get(v_snd_3403_, 0);
v_snd_3408_ = lean_ctor_get(v_snd_3403_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_snd_3403_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3410_ = v_snd_3403_;
v_isShared_3411_ = v_isSharedCheck_3443_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_snd_3408_);
lean_inc(v_fst_3407_);
lean_dec(v_snd_3403_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3443_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_a_3412_; lean_object* v_p_3413_; lean_object* v___x_3414_; lean_object* v_a_3416_; lean_object* v_b_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_a_3412_ = lean_array_uget(v_as_3398_, v_i_3400_);
v_p_3413_ = lean_ctor_get(v_a_3412_, 0);
v___x_3414_ = lean_box(0);
v_b_3423_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3413_, v_x_3397_);
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_3425_ = lean_int_dec_eq(v_b_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3427_; 
lean_inc(v_a_3412_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v_a_3412_);
lean_ctor_set(v___x_3405_, 0, v_b_3423_);
v___x_3427_ = v___x_3405_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_b_3423_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_a_3412_);
v___x_3427_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v_a_3412_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3436_ = lean_ctor_get(v_a_3412_, 1);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_a_3412_, 0);
lean_dec(v_unused_3437_);
v___x_3429_ = v_a_3412_;
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v_a_3412_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_todo_3431_; lean_object* v___x_3433_; 
v_todo_3431_ = lean_array_push(v_snd_3408_, v___x_3427_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v_todo_3431_);
lean_ctor_set(v___x_3429_, 0, v_fst_3407_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_fst_3407_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_todo_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
v_a_3416_ = v___x_3433_;
goto v___jp_3415_;
}
}
}
}
else
{
lean_object* v_cs_x27_3439_; lean_object* v___x_3441_; 
lean_dec(v_b_3423_);
v_cs_x27_3439_ = l_Lean_PersistentArray_push___redArg(v_fst_3407_, v_a_3412_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v_snd_3408_);
lean_ctor_set(v___x_3405_, 0, v_cs_x27_3439_);
v___x_3441_ = v___x_3405_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_cs_x27_3439_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_snd_3408_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v_a_3416_ = v___x_3441_;
goto v___jp_3415_;
}
}
v___jp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_a_3416_);
lean_ctor_set(v___x_3410_, 0, v___x_3414_);
v___x_3418_ = v___x_3410_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_a_3416_);
v___x_3418_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
size_t v___x_3419_; size_t v___x_3420_; 
v___x_3419_ = ((size_t)1ULL);
v___x_3420_ = lean_usize_add(v_i_3400_, v___x_3419_);
v_i_3400_ = v___x_3420_;
v_b_3401_ = v___x_3418_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3446_, lean_object* v_as_3447_, lean_object* v_sz_3448_, lean_object* v_i_3449_, lean_object* v_b_3450_){
_start:
{
size_t v_sz_boxed_3451_; size_t v_i_boxed_3452_; lean_object* v_res_3453_; 
v_sz_boxed_3451_ = lean_unbox_usize(v_sz_3448_);
lean_dec(v_sz_3448_);
v_i_boxed_3452_ = lean_unbox_usize(v_i_3449_);
lean_dec(v_i_3449_);
v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3446_, v_as_3447_, v_sz_boxed_3451_, v_i_boxed_3452_, v_b_3450_);
lean_dec_ref(v_as_3447_);
lean_dec(v_x_3446_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3454_, lean_object* v_as_3455_, size_t v_sz_3456_, size_t v_i_3457_, lean_object* v_b_3458_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3457_, v_sz_3456_);
if (v___x_3459_ == 0)
{
return v_b_3458_;
}
else
{
lean_object* v_snd_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3501_; 
v_snd_3460_ = lean_ctor_get(v_b_3458_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_b_3458_);
if (v_isSharedCheck_3501_ == 0)
{
lean_object* v_unused_3502_; 
v_unused_3502_ = lean_ctor_get(v_b_3458_, 0);
lean_dec(v_unused_3502_);
v___x_3462_ = v_b_3458_;
v_isShared_3463_ = v_isSharedCheck_3501_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_snd_3460_);
lean_dec(v_b_3458_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3501_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_fst_3464_; lean_object* v_snd_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3500_; 
v_fst_3464_ = lean_ctor_get(v_snd_3460_, 0);
v_snd_3465_ = lean_ctor_get(v_snd_3460_, 1);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_snd_3460_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3467_ = v_snd_3460_;
v_isShared_3468_ = v_isSharedCheck_3500_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_snd_3465_);
lean_inc(v_fst_3464_);
lean_dec(v_snd_3460_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3500_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_a_3469_; lean_object* v_p_3470_; lean_object* v___x_3471_; lean_object* v_a_3473_; lean_object* v_b_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v_a_3469_ = lean_array_uget(v_as_3455_, v_i_3457_);
v_p_3470_ = lean_ctor_get(v_a_3469_, 0);
v___x_3471_ = lean_box(0);
v_b_3480_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3470_, v_x_3454_);
v___x_3481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_3482_ = lean_int_dec_eq(v_b_3480_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3484_; 
lean_inc(v_a_3469_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v_a_3469_);
lean_ctor_set(v___x_3462_, 0, v_b_3480_);
v___x_3484_ = v___x_3462_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_b_3480_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_a_3469_);
v___x_3484_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3492_; 
v_isSharedCheck_3492_ = !lean_is_exclusive(v_a_3469_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; lean_object* v_unused_3494_; 
v_unused_3493_ = lean_ctor_get(v_a_3469_, 1);
lean_dec(v_unused_3493_);
v_unused_3494_ = lean_ctor_get(v_a_3469_, 0);
lean_dec(v_unused_3494_);
v___x_3486_ = v_a_3469_;
v_isShared_3487_ = v_isSharedCheck_3492_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v_a_3469_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3492_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v_todo_3488_; lean_object* v___x_3490_; 
v_todo_3488_ = lean_array_push(v_snd_3465_, v___x_3484_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v_todo_3488_);
lean_ctor_set(v___x_3486_, 0, v_fst_3464_);
v___x_3490_ = v___x_3486_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_fst_3464_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_todo_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
v_a_3473_ = v___x_3490_;
goto v___jp_3472_;
}
}
}
}
else
{
lean_object* v_cs_x27_3496_; lean_object* v___x_3498_; 
lean_dec(v_b_3480_);
v_cs_x27_3496_ = l_Lean_PersistentArray_push___redArg(v_fst_3464_, v_a_3469_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v_snd_3465_);
lean_ctor_set(v___x_3462_, 0, v_cs_x27_3496_);
v___x_3498_ = v___x_3462_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_cs_x27_3496_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_snd_3465_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
v_a_3473_ = v___x_3498_;
goto v___jp_3472_;
}
}
v___jp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v_a_3473_);
lean_ctor_set(v___x_3467_, 0, v___x_3471_);
v___x_3475_ = v___x_3467_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_a_3473_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
size_t v___x_3476_; size_t v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = ((size_t)1ULL);
v___x_3477_ = lean_usize_add(v_i_3457_, v___x_3476_);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3454_, v_as_3455_, v_sz_3456_, v___x_3477_, v___x_3475_);
return v___x_3478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3503_, lean_object* v_as_3504_, lean_object* v_sz_3505_, lean_object* v_i_3506_, lean_object* v_b_3507_){
_start:
{
size_t v_sz_boxed_3508_; size_t v_i_boxed_3509_; lean_object* v_res_3510_; 
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3505_);
lean_dec(v_sz_3505_);
v_i_boxed_3509_ = lean_unbox_usize(v_i_3506_);
lean_dec(v_i_3506_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3503_, v_as_3504_, v_sz_boxed_3508_, v_i_boxed_3509_, v_b_3507_);
lean_dec_ref(v_as_3504_);
lean_dec(v_x_3503_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3511_, lean_object* v_as_3512_, size_t v_sz_3513_, size_t v_i_3514_, lean_object* v_b_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3514_, v_sz_3513_);
if (v___x_3516_ == 0)
{
return v_b_3515_;
}
else
{
lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3558_; 
v_snd_3517_ = lean_ctor_get(v_b_3515_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_b_3515_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_b_3515_, 0);
lean_dec(v_unused_3559_);
v___x_3519_ = v_b_3515_;
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_dec(v_b_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3557_; 
v_fst_3521_ = lean_ctor_get(v_snd_3517_, 0);
v_snd_3522_ = lean_ctor_get(v_snd_3517_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_snd_3517_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3524_ = v_snd_3517_;
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_snd_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_a_3526_; lean_object* v_p_3527_; lean_object* v___x_3528_; lean_object* v_a_3530_; lean_object* v_b_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_a_3526_ = lean_array_uget(v_as_3512_, v_i_3514_);
v_p_3527_ = lean_ctor_get(v_a_3526_, 0);
v___x_3528_ = lean_box(0);
v_b_3537_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3527_, v_x_3511_);
v___x_3538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_3539_ = lean_int_dec_eq(v_b_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3541_; 
lean_inc(v_a_3526_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_a_3526_);
lean_ctor_set(v___x_3519_, 0, v_b_3537_);
v___x_3541_ = v___x_3519_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_b_3537_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3526_);
v___x_3541_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3549_; 
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3526_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; lean_object* v_unused_3551_; 
v_unused_3550_ = lean_ctor_get(v_a_3526_, 1);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_a_3526_, 0);
lean_dec(v_unused_3551_);
v___x_3543_ = v_a_3526_;
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
else
{
lean_dec(v_a_3526_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_todo_3545_; lean_object* v___x_3547_; 
v_todo_3545_ = lean_array_push(v_snd_3522_, v___x_3541_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v_todo_3545_);
lean_ctor_set(v___x_3543_, 0, v_fst_3521_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_fst_3521_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_todo_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
v_a_3530_ = v___x_3547_;
goto v___jp_3529_;
}
}
}
}
else
{
lean_object* v_cs_x27_3553_; lean_object* v___x_3555_; 
lean_dec(v_b_3537_);
v_cs_x27_3553_ = l_Lean_PersistentArray_push___redArg(v_fst_3521_, v_a_3526_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_snd_3522_);
lean_ctor_set(v___x_3519_, 0, v_cs_x27_3553_);
v___x_3555_ = v___x_3519_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_cs_x27_3553_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_snd_3522_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
v_a_3530_ = v___x_3555_;
goto v___jp_3529_;
}
}
v___jp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_a_3530_);
lean_ctor_set(v___x_3524_, 0, v___x_3528_);
v___x_3532_ = v___x_3524_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_a_3530_);
v___x_3532_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
size_t v___x_3533_; size_t v___x_3534_; 
v___x_3533_ = ((size_t)1ULL);
v___x_3534_ = lean_usize_add(v_i_3514_, v___x_3533_);
v_i_3514_ = v___x_3534_;
v_b_3515_ = v___x_3532_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3560_, lean_object* v_as_3561_, lean_object* v_sz_3562_, lean_object* v_i_3563_, lean_object* v_b_3564_){
_start:
{
size_t v_sz_boxed_3565_; size_t v_i_boxed_3566_; lean_object* v_res_3567_; 
v_sz_boxed_3565_ = lean_unbox_usize(v_sz_3562_);
lean_dec(v_sz_3562_);
v_i_boxed_3566_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_res_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3560_, v_as_3561_, v_sz_boxed_3565_, v_i_boxed_3566_, v_b_3564_);
lean_dec_ref(v_as_3561_);
lean_dec(v_x_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3568_, lean_object* v_as_3569_, size_t v_sz_3570_, size_t v_i_3571_, lean_object* v_b_3572_){
_start:
{
uint8_t v___x_3573_; 
v___x_3573_ = lean_usize_dec_lt(v_i_3571_, v_sz_3570_);
if (v___x_3573_ == 0)
{
return v_b_3572_;
}
else
{
lean_object* v_snd_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3615_; 
v_snd_3574_ = lean_ctor_get(v_b_3572_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_b_3572_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_b_3572_, 0);
lean_dec(v_unused_3616_);
v___x_3576_ = v_b_3572_;
v_isShared_3577_ = v_isSharedCheck_3615_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3574_);
lean_dec(v_b_3572_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3615_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_fst_3578_; lean_object* v_snd_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3614_; 
v_fst_3578_ = lean_ctor_get(v_snd_3574_, 0);
v_snd_3579_ = lean_ctor_get(v_snd_3574_, 1);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_snd_3574_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3581_ = v_snd_3574_;
v_isShared_3582_ = v_isSharedCheck_3614_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_snd_3579_);
lean_inc(v_fst_3578_);
lean_dec(v_snd_3574_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3614_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_a_3583_; lean_object* v_p_3584_; lean_object* v___x_3585_; lean_object* v_a_3587_; lean_object* v_b_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_a_3583_ = lean_array_uget(v_as_3569_, v_i_3571_);
v_p_3584_ = lean_ctor_get(v_a_3583_, 0);
v___x_3585_ = lean_box(0);
v_b_3594_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3584_, v_x_3568_);
v___x_3595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_3596_ = lean_int_dec_eq(v_b_3594_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3598_; 
lean_inc(v_a_3583_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v_a_3583_);
lean_ctor_set(v___x_3576_, 0, v_b_3594_);
v___x_3598_ = v___x_3576_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_b_3594_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_a_3583_);
v___x_3598_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; lean_object* v_unused_3608_; 
v_unused_3607_ = lean_ctor_get(v_a_3583_, 1);
lean_dec(v_unused_3607_);
v_unused_3608_ = lean_ctor_get(v_a_3583_, 0);
lean_dec(v_unused_3608_);
v___x_3600_ = v_a_3583_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v_a_3583_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v_todo_3602_; lean_object* v___x_3604_; 
v_todo_3602_ = lean_array_push(v_snd_3579_, v___x_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 1, v_todo_3602_);
lean_ctor_set(v___x_3600_, 0, v_fst_3578_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_fst_3578_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_todo_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
v_a_3587_ = v___x_3604_;
goto v___jp_3586_;
}
}
}
}
else
{
lean_object* v_cs_x27_3610_; lean_object* v___x_3612_; 
lean_dec(v_b_3594_);
v_cs_x27_3610_ = l_Lean_PersistentArray_push___redArg(v_fst_3578_, v_a_3583_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v_snd_3579_);
lean_ctor_set(v___x_3576_, 0, v_cs_x27_3610_);
v___x_3612_ = v___x_3576_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_cs_x27_3610_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_snd_3579_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
v_a_3587_ = v___x_3612_;
goto v___jp_3586_;
}
}
v___jp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_a_3587_);
lean_ctor_set(v___x_3581_, 0, v___x_3585_);
v___x_3589_ = v___x_3581_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_a_3587_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = ((size_t)1ULL);
v___x_3591_ = lean_usize_add(v_i_3571_, v___x_3590_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3568_, v_as_3569_, v_sz_3570_, v___x_3591_, v___x_3589_);
return v___x_3592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3617_, lean_object* v_as_3618_, lean_object* v_sz_3619_, lean_object* v_i_3620_, lean_object* v_b_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3619_);
lean_dec(v_sz_3619_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3620_);
lean_dec(v_i_3620_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3617_, v_as_3618_, v_sz_boxed_3622_, v_i_boxed_3623_, v_b_3621_);
lean_dec_ref(v_as_3618_);
lean_dec(v_x_3617_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_x_3625_, lean_object* v_inh_3626_, lean_object* v_n_3627_, lean_object* v_b_3628_){
_start:
{
if (lean_obj_tag(v_n_3627_) == 0)
{
lean_object* v_cs_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3644_; 
v_cs_3629_ = lean_ctor_get(v_n_3627_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_n_3627_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3631_ = v_n_3627_;
v_isShared_3632_ = v_isSharedCheck_3644_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_cs_3629_);
lean_dec(v_n_3627_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3644_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; size_t v_sz_3635_; size_t v___x_3636_; lean_object* v___x_3637_; lean_object* v_fst_3638_; 
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_b_3628_);
v_sz_3635_ = lean_array_size(v_cs_3629_);
v___x_3636_ = ((size_t)0ULL);
v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3625_, v_inh_3626_, v_cs_3629_, v_sz_3635_, v___x_3636_, v___x_3634_);
lean_dec_ref(v_cs_3629_);
v_fst_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_fst_3638_);
if (lean_obj_tag(v_fst_3638_) == 0)
{
lean_object* v_snd_3639_; lean_object* v___x_3641_; 
v_snd_3639_ = lean_ctor_get(v___x_3637_, 1);
lean_inc(v_snd_3639_);
lean_dec_ref(v___x_3637_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 1);
lean_ctor_set(v___x_3631_, 0, v_snd_3639_);
v___x_3641_ = v___x_3631_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_snd_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
else
{
lean_object* v_val_3643_; 
lean_dec_ref(v___x_3637_);
lean_del_object(v___x_3631_);
v_val_3643_ = lean_ctor_get(v_fst_3638_, 0);
lean_inc(v_val_3643_);
lean_dec_ref(v_fst_3638_);
return v_val_3643_;
}
}
}
else
{
lean_object* v_vs_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3660_; 
v_vs_3645_ = lean_ctor_get(v_n_3627_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_n_3627_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3647_ = v_n_3627_;
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_vs_3645_);
lean_dec(v_n_3627_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; size_t v_sz_3651_; size_t v___x_3652_; lean_object* v___x_3653_; lean_object* v_fst_3654_; 
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set(v___x_3650_, 1, v_b_3628_);
v_sz_3651_ = lean_array_size(v_vs_3645_);
v___x_3652_ = ((size_t)0ULL);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3625_, v_vs_3645_, v_sz_3651_, v___x_3652_, v___x_3650_);
lean_dec_ref(v_vs_3645_);
v_fst_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_fst_3654_);
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v_snd_3655_; lean_object* v___x_3657_; 
v_snd_3655_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_snd_3655_);
lean_dec_ref(v___x_3653_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v_snd_3655_);
v___x_3657_ = v___x_3647_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_snd_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
else
{
lean_object* v_val_3659_; 
lean_dec_ref(v___x_3653_);
lean_del_object(v___x_3647_);
v_val_3659_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3659_);
lean_dec_ref(v_fst_3654_);
return v_val_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_3661_, lean_object* v_inh_3662_, lean_object* v_as_3663_, size_t v_sz_3664_, size_t v_i_3665_, lean_object* v_b_3666_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = lean_usize_dec_lt(v_i_3665_, v_sz_3664_);
if (v___x_3667_ == 0)
{
return v_b_3666_;
}
else
{
lean_object* v_snd_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3686_; 
v_snd_3668_ = lean_ctor_get(v_b_3666_, 1);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_b_3666_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v_b_3666_, 0);
lean_dec(v_unused_3687_);
v___x_3670_ = v_b_3666_;
v_isShared_3671_ = v_isSharedCheck_3686_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_snd_3668_);
lean_dec(v_b_3666_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3686_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_a_3672_; lean_object* v___x_3673_; 
v_a_3672_ = lean_array_uget_borrowed(v_as_3663_, v_i_3665_);
lean_inc(v_snd_3668_);
lean_inc(v_a_3672_);
v___x_3673_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3661_, v_inh_3662_, v_a_3672_, v_snd_3668_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3674_);
v___x_3676_ = v___x_3670_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_snd_3668_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
lean_dec(v_snd_3668_);
v_a_3678_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3673_);
v___x_3679_ = lean_box(0);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 1, v_a_3678_);
lean_ctor_set(v___x_3670_, 0, v___x_3679_);
v___x_3681_ = v___x_3670_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_a_3678_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
size_t v___x_3682_; size_t v___x_3683_; 
v___x_3682_ = ((size_t)1ULL);
v___x_3683_ = lean_usize_add(v_i_3665_, v___x_3682_);
v_i_3665_ = v___x_3683_;
v_b_3666_ = v___x_3681_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_3688_, lean_object* v_inh_3689_, lean_object* v_as_3690_, lean_object* v_sz_3691_, lean_object* v_i_3692_, lean_object* v_b_3693_){
_start:
{
size_t v_sz_boxed_3694_; size_t v_i_boxed_3695_; lean_object* v_res_3696_; 
v_sz_boxed_3694_ = lean_unbox_usize(v_sz_3691_);
lean_dec(v_sz_3691_);
v_i_boxed_3695_ = lean_unbox_usize(v_i_3692_);
lean_dec(v_i_3692_);
v_res_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3688_, v_inh_3689_, v_as_3690_, v_sz_boxed_3694_, v_i_boxed_3695_, v_b_3693_);
lean_dec_ref(v_as_3690_);
lean_dec_ref(v_inh_3689_);
lean_dec(v_x_3688_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3697_, lean_object* v_inh_3698_, lean_object* v_n_3699_, lean_object* v_b_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3697_, v_inh_3698_, v_n_3699_, v_b_3700_);
lean_dec_ref(v_inh_3698_);
lean_dec(v_x_3697_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3702_, lean_object* v_t_3703_, lean_object* v_init_3704_){
_start:
{
lean_object* v_root_3705_; lean_object* v_tail_3706_; lean_object* v___x_3707_; 
v_root_3705_ = lean_ctor_get(v_t_3703_, 0);
lean_inc_ref(v_root_3705_);
v_tail_3706_ = lean_ctor_get(v_t_3703_, 1);
lean_inc_ref(v_tail_3706_);
lean_dec_ref(v_t_3703_);
lean_inc_ref(v_init_3704_);
v___x_3707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3702_, v_init_3704_, v_root_3705_, v_init_3704_);
lean_dec_ref(v_init_3704_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; 
lean_dec_ref(v_tail_3706_);
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
return v_a_3708_;
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; size_t v_sz_3712_; size_t v___x_3713_; lean_object* v___x_3714_; lean_object* v_fst_3715_; 
v_a_3709_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3707_);
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
lean_ctor_set(v___x_3711_, 1, v_a_3709_);
v_sz_3712_ = lean_array_size(v_tail_3706_);
v___x_3713_ = ((size_t)0ULL);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3702_, v_tail_3706_, v_sz_3712_, v___x_3713_, v___x_3711_);
lean_dec_ref(v_tail_3706_);
v_fst_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_fst_3715_);
if (lean_obj_tag(v_fst_3715_) == 0)
{
lean_object* v_snd_3716_; 
v_snd_3716_ = lean_ctor_get(v___x_3714_, 1);
lean_inc(v_snd_3716_);
lean_dec_ref(v___x_3714_);
return v_snd_3716_;
}
else
{
lean_object* v_val_3717_; 
lean_dec_ref(v___x_3714_);
v_val_3717_ = lean_ctor_get(v_fst_3715_, 0);
lean_inc(v_val_3717_);
lean_dec_ref(v_fst_3715_);
return v_val_3717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3718_, lean_object* v_t_3719_, lean_object* v_init_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3718_, v_t_3719_, v_init_3720_);
lean_dec(v_x_3718_);
return v_res_3721_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(32u);
v___x_3723_ = lean_mk_empty_array_with_capacity(v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v_cs_x27_3730_; 
v___x_3725_ = ((size_t)5ULL);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_unsigned_to_nat(32u);
v___x_3728_ = lean_mk_empty_array_with_capacity(v___x_3727_);
v___x_3729_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3730_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3730_, 0, v___x_3729_);
lean_ctor_set(v_cs_x27_3730_, 1, v___x_3728_);
lean_ctor_set(v_cs_x27_3730_, 2, v___x_3726_);
lean_ctor_set(v_cs_x27_3730_, 3, v___x_3726_);
lean_ctor_set_usize(v_cs_x27_3730_, 4, v___x_3725_);
return v_cs_x27_3730_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3733_; lean_object* v_cs_x27_3734_; lean_object* v___x_3735_; 
v_todo_3733_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3734_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_cs_x27_3734_);
lean_ctor_set(v___x_3735_, 1, v_todo_3733_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3736_, lean_object* v_cs_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_fst_3740_; lean_object* v_snd_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v___x_3738_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3739_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3736_, v_cs_3737_, v___x_3738_);
v_fst_3740_ = lean_ctor_get(v___x_3739_, 0);
v_snd_3741_ = lean_ctor_get(v___x_3739_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3739_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_snd_3741_);
lean_inc(v_fst_3740_);
lean_dec(v___x_3739_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_fst_3740_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_snd_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3749_, lean_object* v_cs_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3749_, v_cs_3750_);
lean_dec(v_x_3749_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3752_, lean_object* v_cs_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3752_, v_cs_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3755_, lean_object* v_cs_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3755_, v_cs_3756_);
lean_dec(v_x_3755_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3758_, lean_object* v_y_3759_, lean_object* v_fst_3760_, lean_object* v_s_3761_){
_start:
{
lean_object* v_structs_3762_; lean_object* v_typeIdOf_3763_; lean_object* v_exprToStructId_3764_; lean_object* v_exprToStructIdEntries_3765_; lean_object* v_forbiddenNatModules_3766_; lean_object* v_natStructs_3767_; lean_object* v_natTypeIdOf_3768_; lean_object* v_exprToNatStructId_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_structs_3762_ = lean_ctor_get(v_s_3761_, 0);
v_typeIdOf_3763_ = lean_ctor_get(v_s_3761_, 1);
v_exprToStructId_3764_ = lean_ctor_get(v_s_3761_, 2);
v_exprToStructIdEntries_3765_ = lean_ctor_get(v_s_3761_, 3);
v_forbiddenNatModules_3766_ = lean_ctor_get(v_s_3761_, 4);
v_natStructs_3767_ = lean_ctor_get(v_s_3761_, 5);
v_natTypeIdOf_3768_ = lean_ctor_get(v_s_3761_, 6);
v_exprToNatStructId_3769_ = lean_ctor_get(v_s_3761_, 7);
v___x_3770_ = lean_array_get_size(v_structs_3762_);
v___x_3771_ = lean_nat_dec_lt(v_a_3758_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec_ref(v_fst_3760_);
return v_s_3761_;
}
else
{
lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3833_; 
lean_inc_ref(v_exprToNatStructId_3769_);
lean_inc_ref(v_natTypeIdOf_3768_);
lean_inc_ref(v_natStructs_3767_);
lean_inc_ref(v_forbiddenNatModules_3766_);
lean_inc_ref(v_exprToStructIdEntries_3765_);
lean_inc_ref(v_exprToStructId_3764_);
lean_inc_ref(v_typeIdOf_3763_);
lean_inc_ref(v_structs_3762_);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_s_3761_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; 
v_unused_3834_ = lean_ctor_get(v_s_3761_, 7);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_s_3761_, 6);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_s_3761_, 5);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_s_3761_, 4);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_s_3761_, 3);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_s_3761_, 2);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_s_3761_, 1);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_s_3761_, 0);
lean_dec(v_unused_3841_);
v___x_3773_ = v_s_3761_;
v_isShared_3774_ = v_isSharedCheck_3833_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v_s_3761_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3833_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v_v_3775_; lean_object* v_id_3776_; lean_object* v_ringId_x3f_3777_; lean_object* v_type_3778_; lean_object* v_u_3779_; lean_object* v_intModuleInst_3780_; lean_object* v_leInst_x3f_3781_; lean_object* v_ltInst_x3f_3782_; lean_object* v_lawfulOrderLTInst_x3f_3783_; lean_object* v_isPreorderInst_x3f_3784_; lean_object* v_orderedAddInst_x3f_3785_; lean_object* v_isLinearInst_x3f_3786_; lean_object* v_noNatDivInst_x3f_3787_; lean_object* v_ringInst_x3f_3788_; lean_object* v_commRingInst_x3f_3789_; lean_object* v_orderedRingInst_x3f_3790_; lean_object* v_fieldInst_x3f_3791_; lean_object* v_charInst_x3f_3792_; lean_object* v_zero_3793_; lean_object* v_ofNatZero_3794_; lean_object* v_one_x3f_3795_; lean_object* v_leFn_x3f_3796_; lean_object* v_ltFn_x3f_3797_; lean_object* v_addFn_3798_; lean_object* v_zsmulFn_3799_; lean_object* v_nsmulFn_3800_; lean_object* v_zsmulFn_x3f_3801_; lean_object* v_nsmulFn_x3f_3802_; lean_object* v_homomulFn_x3f_3803_; lean_object* v_subFn_3804_; lean_object* v_negFn_3805_; lean_object* v_vars_3806_; lean_object* v_varMap_3807_; lean_object* v_lowers_3808_; lean_object* v_uppers_3809_; lean_object* v_diseqs_3810_; lean_object* v_assignment_3811_; uint8_t v_caseSplits_3812_; lean_object* v_conflict_x3f_3813_; lean_object* v_diseqSplits_3814_; lean_object* v_elimEqs_3815_; lean_object* v_elimStack_3816_; lean_object* v_occurs_3817_; lean_object* v_ignored_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3832_; 
v_v_3775_ = lean_array_fget(v_structs_3762_, v_a_3758_);
v_id_3776_ = lean_ctor_get(v_v_3775_, 0);
v_ringId_x3f_3777_ = lean_ctor_get(v_v_3775_, 1);
v_type_3778_ = lean_ctor_get(v_v_3775_, 2);
v_u_3779_ = lean_ctor_get(v_v_3775_, 3);
v_intModuleInst_3780_ = lean_ctor_get(v_v_3775_, 4);
v_leInst_x3f_3781_ = lean_ctor_get(v_v_3775_, 5);
v_ltInst_x3f_3782_ = lean_ctor_get(v_v_3775_, 6);
v_lawfulOrderLTInst_x3f_3783_ = lean_ctor_get(v_v_3775_, 7);
v_isPreorderInst_x3f_3784_ = lean_ctor_get(v_v_3775_, 8);
v_orderedAddInst_x3f_3785_ = lean_ctor_get(v_v_3775_, 9);
v_isLinearInst_x3f_3786_ = lean_ctor_get(v_v_3775_, 10);
v_noNatDivInst_x3f_3787_ = lean_ctor_get(v_v_3775_, 11);
v_ringInst_x3f_3788_ = lean_ctor_get(v_v_3775_, 12);
v_commRingInst_x3f_3789_ = lean_ctor_get(v_v_3775_, 13);
v_orderedRingInst_x3f_3790_ = lean_ctor_get(v_v_3775_, 14);
v_fieldInst_x3f_3791_ = lean_ctor_get(v_v_3775_, 15);
v_charInst_x3f_3792_ = lean_ctor_get(v_v_3775_, 16);
v_zero_3793_ = lean_ctor_get(v_v_3775_, 17);
v_ofNatZero_3794_ = lean_ctor_get(v_v_3775_, 18);
v_one_x3f_3795_ = lean_ctor_get(v_v_3775_, 19);
v_leFn_x3f_3796_ = lean_ctor_get(v_v_3775_, 20);
v_ltFn_x3f_3797_ = lean_ctor_get(v_v_3775_, 21);
v_addFn_3798_ = lean_ctor_get(v_v_3775_, 22);
v_zsmulFn_3799_ = lean_ctor_get(v_v_3775_, 23);
v_nsmulFn_3800_ = lean_ctor_get(v_v_3775_, 24);
v_zsmulFn_x3f_3801_ = lean_ctor_get(v_v_3775_, 25);
v_nsmulFn_x3f_3802_ = lean_ctor_get(v_v_3775_, 26);
v_homomulFn_x3f_3803_ = lean_ctor_get(v_v_3775_, 27);
v_subFn_3804_ = lean_ctor_get(v_v_3775_, 28);
v_negFn_3805_ = lean_ctor_get(v_v_3775_, 29);
v_vars_3806_ = lean_ctor_get(v_v_3775_, 30);
v_varMap_3807_ = lean_ctor_get(v_v_3775_, 31);
v_lowers_3808_ = lean_ctor_get(v_v_3775_, 32);
v_uppers_3809_ = lean_ctor_get(v_v_3775_, 33);
v_diseqs_3810_ = lean_ctor_get(v_v_3775_, 34);
v_assignment_3811_ = lean_ctor_get(v_v_3775_, 35);
v_caseSplits_3812_ = lean_ctor_get_uint8(v_v_3775_, sizeof(void*)*42);
v_conflict_x3f_3813_ = lean_ctor_get(v_v_3775_, 36);
v_diseqSplits_3814_ = lean_ctor_get(v_v_3775_, 37);
v_elimEqs_3815_ = lean_ctor_get(v_v_3775_, 38);
v_elimStack_3816_ = lean_ctor_get(v_v_3775_, 39);
v_occurs_3817_ = lean_ctor_get(v_v_3775_, 40);
v_ignored_3818_ = lean_ctor_get(v_v_3775_, 41);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_v_3775_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3820_ = v_v_3775_;
v_isShared_3821_ = v_isSharedCheck_3832_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_ignored_3818_);
lean_inc(v_occurs_3817_);
lean_inc(v_elimStack_3816_);
lean_inc(v_elimEqs_3815_);
lean_inc(v_diseqSplits_3814_);
lean_inc(v_conflict_x3f_3813_);
lean_inc(v_assignment_3811_);
lean_inc(v_diseqs_3810_);
lean_inc(v_uppers_3809_);
lean_inc(v_lowers_3808_);
lean_inc(v_varMap_3807_);
lean_inc(v_vars_3806_);
lean_inc(v_negFn_3805_);
lean_inc(v_subFn_3804_);
lean_inc(v_homomulFn_x3f_3803_);
lean_inc(v_nsmulFn_x3f_3802_);
lean_inc(v_zsmulFn_x3f_3801_);
lean_inc(v_nsmulFn_3800_);
lean_inc(v_zsmulFn_3799_);
lean_inc(v_addFn_3798_);
lean_inc(v_ltFn_x3f_3797_);
lean_inc(v_leFn_x3f_3796_);
lean_inc(v_one_x3f_3795_);
lean_inc(v_ofNatZero_3794_);
lean_inc(v_zero_3793_);
lean_inc(v_charInst_x3f_3792_);
lean_inc(v_fieldInst_x3f_3791_);
lean_inc(v_orderedRingInst_x3f_3790_);
lean_inc(v_commRingInst_x3f_3789_);
lean_inc(v_ringInst_x3f_3788_);
lean_inc(v_noNatDivInst_x3f_3787_);
lean_inc(v_isLinearInst_x3f_3786_);
lean_inc(v_orderedAddInst_x3f_3785_);
lean_inc(v_isPreorderInst_x3f_3784_);
lean_inc(v_lawfulOrderLTInst_x3f_3783_);
lean_inc(v_ltInst_x3f_3782_);
lean_inc(v_leInst_x3f_3781_);
lean_inc(v_intModuleInst_3780_);
lean_inc(v_u_3779_);
lean_inc(v_type_3778_);
lean_inc(v_ringId_x3f_3777_);
lean_inc(v_id_3776_);
lean_dec(v_v_3775_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3832_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v_xs_x27_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3822_ = lean_box(0);
v_xs_x27_3823_ = lean_array_fset(v_structs_3762_, v_a_3758_, v___x_3822_);
v___x_3824_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3810_, v_y_3759_, v_fst_3760_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 34, v___x_3824_);
v___x_3826_ = v___x_3820_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_id_3776_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_ringId_x3f_3777_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_type_3778_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_u_3779_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_intModuleInst_3780_);
lean_ctor_set(v_reuseFailAlloc_3831_, 5, v_leInst_x3f_3781_);
lean_ctor_set(v_reuseFailAlloc_3831_, 6, v_ltInst_x3f_3782_);
lean_ctor_set(v_reuseFailAlloc_3831_, 7, v_lawfulOrderLTInst_x3f_3783_);
lean_ctor_set(v_reuseFailAlloc_3831_, 8, v_isPreorderInst_x3f_3784_);
lean_ctor_set(v_reuseFailAlloc_3831_, 9, v_orderedAddInst_x3f_3785_);
lean_ctor_set(v_reuseFailAlloc_3831_, 10, v_isLinearInst_x3f_3786_);
lean_ctor_set(v_reuseFailAlloc_3831_, 11, v_noNatDivInst_x3f_3787_);
lean_ctor_set(v_reuseFailAlloc_3831_, 12, v_ringInst_x3f_3788_);
lean_ctor_set(v_reuseFailAlloc_3831_, 13, v_commRingInst_x3f_3789_);
lean_ctor_set(v_reuseFailAlloc_3831_, 14, v_orderedRingInst_x3f_3790_);
lean_ctor_set(v_reuseFailAlloc_3831_, 15, v_fieldInst_x3f_3791_);
lean_ctor_set(v_reuseFailAlloc_3831_, 16, v_charInst_x3f_3792_);
lean_ctor_set(v_reuseFailAlloc_3831_, 17, v_zero_3793_);
lean_ctor_set(v_reuseFailAlloc_3831_, 18, v_ofNatZero_3794_);
lean_ctor_set(v_reuseFailAlloc_3831_, 19, v_one_x3f_3795_);
lean_ctor_set(v_reuseFailAlloc_3831_, 20, v_leFn_x3f_3796_);
lean_ctor_set(v_reuseFailAlloc_3831_, 21, v_ltFn_x3f_3797_);
lean_ctor_set(v_reuseFailAlloc_3831_, 22, v_addFn_3798_);
lean_ctor_set(v_reuseFailAlloc_3831_, 23, v_zsmulFn_3799_);
lean_ctor_set(v_reuseFailAlloc_3831_, 24, v_nsmulFn_3800_);
lean_ctor_set(v_reuseFailAlloc_3831_, 25, v_zsmulFn_x3f_3801_);
lean_ctor_set(v_reuseFailAlloc_3831_, 26, v_nsmulFn_x3f_3802_);
lean_ctor_set(v_reuseFailAlloc_3831_, 27, v_homomulFn_x3f_3803_);
lean_ctor_set(v_reuseFailAlloc_3831_, 28, v_subFn_3804_);
lean_ctor_set(v_reuseFailAlloc_3831_, 29, v_negFn_3805_);
lean_ctor_set(v_reuseFailAlloc_3831_, 30, v_vars_3806_);
lean_ctor_set(v_reuseFailAlloc_3831_, 31, v_varMap_3807_);
lean_ctor_set(v_reuseFailAlloc_3831_, 32, v_lowers_3808_);
lean_ctor_set(v_reuseFailAlloc_3831_, 33, v_uppers_3809_);
lean_ctor_set(v_reuseFailAlloc_3831_, 34, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3831_, 35, v_assignment_3811_);
lean_ctor_set(v_reuseFailAlloc_3831_, 36, v_conflict_x3f_3813_);
lean_ctor_set(v_reuseFailAlloc_3831_, 37, v_diseqSplits_3814_);
lean_ctor_set(v_reuseFailAlloc_3831_, 38, v_elimEqs_3815_);
lean_ctor_set(v_reuseFailAlloc_3831_, 39, v_elimStack_3816_);
lean_ctor_set(v_reuseFailAlloc_3831_, 40, v_occurs_3817_);
lean_ctor_set(v_reuseFailAlloc_3831_, 41, v_ignored_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*42, v_caseSplits_3812_);
v___x_3826_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_array_fset(v_xs_x27_3823_, v_a_3758_, v___x_3826_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3827_);
v___x_3829_ = v___x_3773_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_typeIdOf_3763_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_exprToStructId_3764_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_exprToStructIdEntries_3765_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_forbiddenNatModules_3766_);
lean_ctor_set(v_reuseFailAlloc_3830_, 5, v_natStructs_3767_);
lean_ctor_set(v_reuseFailAlloc_3830_, 6, v_natTypeIdOf_3768_);
lean_ctor_set(v_reuseFailAlloc_3830_, 7, v_exprToNatStructId_3769_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3842_, lean_object* v_y_3843_, lean_object* v_fst_3844_, lean_object* v_s_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3842_, v_y_3843_, v_fst_3844_, v_s_3845_);
lean_dec(v_y_3843_);
lean_dec(v_a_3842_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3847_, lean_object* v_x_3848_, lean_object* v_c_3849_, lean_object* v_as_3850_, size_t v_sz_3851_, size_t v_i_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_a_3867_; uint8_t v___x_3871_; 
v___x_3871_ = lean_usize_dec_lt(v_i_3852_, v_sz_3851_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_b_3853_);
return v___x_3872_;
}
else
{
lean_object* v_a_3873_; lean_object* v_fst_3874_; lean_object* v_snd_3875_; lean_object* v___x_3876_; 
lean_dec_ref(v_b_3853_);
v_a_3873_ = lean_array_uget_borrowed(v_as_3850_, v_i_3852_);
v_fst_3874_ = lean_ctor_get(v_a_3873_, 0);
v_snd_3875_ = lean_ctor_get(v_a_3873_, 1);
lean_inc(v_snd_3875_);
lean_inc(v_fst_3874_);
lean_inc_ref(v_c_3849_);
v___x_3876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3847_, v_x_3848_, v_c_3849_, v_fst_3874_, v_snd_3875_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref(v___x_3876_);
v___x_3878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3877_) == 1)
{
lean_object* v_val_3879_; lean_object* v___x_3880_; 
v_val_3879_ = lean_ctor_get(v_a_3877_, 0);
lean_inc(v_val_3879_);
lean_dec_ref(v_a_3877_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc(v___y_3854_);
v___x_3880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3879_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
lean_dec_ref(v___x_3880_);
v___x_3881_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3891_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
uint8_t v___x_3886_; 
v___x_3886_ = lean_unbox(v_a_3882_);
lean_dec(v_a_3882_);
if (v___x_3886_ == 0)
{
lean_del_object(v___x_3884_);
v_a_3867_ = v___x_3878_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v___x_3887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3887_);
v___x_3889_ = v___x_3884_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v_a_3892_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3881_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3881_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v_a_3900_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3880_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3880_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v___x_3908_; 
lean_dec(v_a_3877_);
lean_inc(v___y_3854_);
v___x_3908_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3875_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_dec_ref(v___x_3908_);
v_a_3867_ = v___x_3878_;
goto v___jp_3866_;
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v_c_3849_);
v_a_3917_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3876_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3876_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
v___jp_3866_:
{
size_t v___x_3868_; size_t v___x_3869_; 
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3852_, v___x_3868_);
v_i_3852_ = v___x_3869_;
v_b_3853_ = v_a_3867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3925_ = _args[0];
lean_object* v_x_3926_ = _args[1];
lean_object* v_c_3927_ = _args[2];
lean_object* v_as_3928_ = _args[3];
lean_object* v_sz_3929_ = _args[4];
lean_object* v_i_3930_ = _args[5];
lean_object* v_b_3931_ = _args[6];
lean_object* v___y_3932_ = _args[7];
lean_object* v___y_3933_ = _args[8];
lean_object* v___y_3934_ = _args[9];
lean_object* v___y_3935_ = _args[10];
lean_object* v___y_3936_ = _args[11];
lean_object* v___y_3937_ = _args[12];
lean_object* v___y_3938_ = _args[13];
lean_object* v___y_3939_ = _args[14];
lean_object* v___y_3940_ = _args[15];
lean_object* v___y_3941_ = _args[16];
lean_object* v___y_3942_ = _args[17];
lean_object* v___y_3943_ = _args[18];
_start:
{
size_t v_sz_boxed_3944_; size_t v_i_boxed_3945_; lean_object* v_res_3946_; 
v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3929_);
lean_dec(v_sz_3929_);
v_i_boxed_3945_ = lean_unbox_usize(v_i_3930_);
lean_dec(v_i_3930_);
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3925_, v_x_3926_, v_c_3927_, v_as_3928_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec_ref(v_as_3928_);
lean_dec(v_x_3926_);
lean_dec(v_a_3925_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3947_, lean_object* v_x_3948_, lean_object* v_c_3949_, lean_object* v_y_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4023_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_4023_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4023_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
uint8_t v___x_3968_; 
v___x_3968_ = lean_unbox(v_a_3964_);
lean_dec(v_a_3964_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_del_object(v___x_3966_);
v___x_3969_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___y_3972_; lean_object* v_diseqs_4005_; lean_object* v_size_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v_diseqs_4005_ = lean_ctor_get(v_a_3970_, 34);
lean_inc_ref(v_diseqs_4005_);
lean_dec(v_a_3970_);
v_size_4006_ = lean_ctor_get(v_diseqs_4005_, 2);
v___x_4007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_4008_ = lean_nat_dec_lt(v_y_3950_, v_size_4006_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; 
lean_dec_ref(v_diseqs_4005_);
v___x_4009_ = l_outOfBounds___redArg(v___x_4007_);
v___y_3972_ = v___x_4009_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4007_, v_diseqs_4005_, v_y_3950_);
v___y_3972_ = v___x_4010_;
goto v___jp_3971_;
}
v___jp_3971_:
{
lean_object* v___x_3973_; lean_object* v_fst_3974_; lean_object* v_snd_3975_; lean_object* v___f_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3973_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3948_, v___y_3972_);
v_fst_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_fst_3974_);
v_snd_3975_ = lean_ctor_get(v___x_3973_, 1);
lean_inc(v_snd_3975_);
lean_dec_ref(v___x_3973_);
lean_inc(v_a_3951_);
v___f_3976_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3976_, 0, v_a_3951_);
lean_closure_set(v___f_3976_, 1, v_y_3950_);
lean_closure_set(v___f_3976_, 2, v_fst_3974_);
v___x_3977_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3978_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3977_, v___f_3976_, v_a_3952_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; size_t v_sz_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
lean_dec_ref(v___x_3978_);
v___x_3979_ = lean_box(0);
v___x_3980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3981_ = lean_array_size(v_snd_3975_);
v___x_3982_ = ((size_t)0ULL);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3947_, v_x_3948_, v_c_3949_, v_snd_3975_, v_sz_3981_, v___x_3982_, v___x_3980_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_snd_3975_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3996_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_3996_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3996_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_fst_3988_; 
v_fst_3988_ = lean_ctor_get(v_a_3984_, 0);
lean_inc(v_fst_3988_);
lean_dec(v_a_3984_);
if (lean_obj_tag(v_fst_3988_) == 0)
{
lean_object* v___x_3990_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3979_);
v___x_3990_ = v___x_3986_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3979_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
else
{
lean_object* v_val_3992_; lean_object* v___x_3994_; 
v_val_3992_ = lean_ctor_get(v_fst_3988_, 0);
lean_inc(v_val_3992_);
lean_dec_ref(v_fst_3988_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v_val_3992_);
v___x_3994_ = v___x_3986_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_val_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
v_a_3997_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3983_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3983_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
else
{
lean_dec(v_snd_3975_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec_ref(v_c_3949_);
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec(v_y_3950_);
lean_dec_ref(v_c_3949_);
v_a_4011_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3969_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3969_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4021_; 
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec(v_y_3950_);
lean_dec_ref(v_c_3949_);
v___x_4019_ = lean_box(0);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_4019_);
v___x_4021_ = v___x_3966_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec(v_y_3950_);
lean_dec_ref(v_c_3949_);
v_a_4024_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3963_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_3963_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_4032_, lean_object* v_x_4033_, lean_object* v_c_4034_, lean_object* v_y_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_4032_, v_x_4033_, v_c_4034_, v_y_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
lean_dec(v_x_4033_);
lean_dec(v_a_4032_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_4049_, lean_object* v_x_4050_, lean_object* v_c_4051_, lean_object* v_y_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v___x_4065_; 
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
lean_inc(v_a_4057_);
lean_inc_ref(v_a_4056_);
lean_inc(v_a_4055_);
lean_inc(v_a_4054_);
lean_inc(v_a_4053_);
lean_inc(v_y_4052_);
lean_inc_ref(v_c_4051_);
lean_inc(v_x_4050_);
lean_inc(v_a_4049_);
v___x_4065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_4049_, v_x_4050_, v_c_4051_, v_y_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v___x_4066_; 
lean_dec_ref(v___x_4065_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
lean_inc(v_a_4057_);
lean_inc_ref(v_a_4056_);
lean_inc(v_a_4055_);
lean_inc(v_a_4054_);
lean_inc(v_a_4053_);
lean_inc(v_y_4052_);
lean_inc_ref(v_c_4051_);
lean_inc(v_x_4050_);
lean_inc(v_a_4049_);
v___x_4066_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_4049_, v_x_4050_, v_c_4051_, v_y_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref(v___x_4066_);
v___x_4067_ = lean_nat_to_int(v_a_4049_);
v___x_4068_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_4067_, v_x_4050_, v_c_4051_, v_y_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
lean_dec(v_x_4050_);
lean_dec(v___x_4067_);
return v___x_4068_;
}
else
{
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec(v_y_4052_);
lean_dec_ref(v_c_4051_);
lean_dec(v_x_4050_);
lean_dec(v_a_4049_);
return v___x_4066_;
}
}
else
{
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec(v_y_4052_);
lean_dec_ref(v_c_4051_);
lean_dec(v_x_4050_);
lean_dec(v_a_4049_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_4069_, lean_object* v_x_4070_, lean_object* v_c_4071_, lean_object* v_y_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4069_, v_x_4070_, v_c_4071_, v_y_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_4086_, lean_object* v_x_4087_, lean_object* v_s_4088_){
_start:
{
lean_object* v_structs_4089_; lean_object* v_typeIdOf_4090_; lean_object* v_exprToStructId_4091_; lean_object* v_exprToStructIdEntries_4092_; lean_object* v_forbiddenNatModules_4093_; lean_object* v_natStructs_4094_; lean_object* v_natTypeIdOf_4095_; lean_object* v_exprToNatStructId_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; 
v_structs_4089_ = lean_ctor_get(v_s_4088_, 0);
v_typeIdOf_4090_ = lean_ctor_get(v_s_4088_, 1);
v_exprToStructId_4091_ = lean_ctor_get(v_s_4088_, 2);
v_exprToStructIdEntries_4092_ = lean_ctor_get(v_s_4088_, 3);
v_forbiddenNatModules_4093_ = lean_ctor_get(v_s_4088_, 4);
v_natStructs_4094_ = lean_ctor_get(v_s_4088_, 5);
v_natTypeIdOf_4095_ = lean_ctor_get(v_s_4088_, 6);
v_exprToNatStructId_4096_ = lean_ctor_get(v_s_4088_, 7);
v___x_4097_ = lean_array_get_size(v_structs_4089_);
v___x_4098_ = lean_nat_dec_lt(v_a_4086_, v___x_4097_);
if (v___x_4098_ == 0)
{
return v_s_4088_;
}
else
{
lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4161_; 
lean_inc_ref(v_exprToNatStructId_4096_);
lean_inc_ref(v_natTypeIdOf_4095_);
lean_inc_ref(v_natStructs_4094_);
lean_inc_ref(v_forbiddenNatModules_4093_);
lean_inc_ref(v_exprToStructIdEntries_4092_);
lean_inc_ref(v_exprToStructId_4091_);
lean_inc_ref(v_typeIdOf_4090_);
lean_inc_ref(v_structs_4089_);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_s_4088_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; lean_object* v_unused_4163_; lean_object* v_unused_4164_; lean_object* v_unused_4165_; lean_object* v_unused_4166_; lean_object* v_unused_4167_; lean_object* v_unused_4168_; lean_object* v_unused_4169_; 
v_unused_4162_ = lean_ctor_get(v_s_4088_, 7);
lean_dec(v_unused_4162_);
v_unused_4163_ = lean_ctor_get(v_s_4088_, 6);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_s_4088_, 5);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_s_4088_, 4);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_s_4088_, 3);
lean_dec(v_unused_4166_);
v_unused_4167_ = lean_ctor_get(v_s_4088_, 2);
lean_dec(v_unused_4167_);
v_unused_4168_ = lean_ctor_get(v_s_4088_, 1);
lean_dec(v_unused_4168_);
v_unused_4169_ = lean_ctor_get(v_s_4088_, 0);
lean_dec(v_unused_4169_);
v___x_4100_ = v_s_4088_;
v_isShared_4101_ = v_isSharedCheck_4161_;
goto v_resetjp_4099_;
}
else
{
lean_dec(v_s_4088_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4161_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v_v_4102_; lean_object* v_id_4103_; lean_object* v_ringId_x3f_4104_; lean_object* v_type_4105_; lean_object* v_u_4106_; lean_object* v_intModuleInst_4107_; lean_object* v_leInst_x3f_4108_; lean_object* v_ltInst_x3f_4109_; lean_object* v_lawfulOrderLTInst_x3f_4110_; lean_object* v_isPreorderInst_x3f_4111_; lean_object* v_orderedAddInst_x3f_4112_; lean_object* v_isLinearInst_x3f_4113_; lean_object* v_noNatDivInst_x3f_4114_; lean_object* v_ringInst_x3f_4115_; lean_object* v_commRingInst_x3f_4116_; lean_object* v_orderedRingInst_x3f_4117_; lean_object* v_fieldInst_x3f_4118_; lean_object* v_charInst_x3f_4119_; lean_object* v_zero_4120_; lean_object* v_ofNatZero_4121_; lean_object* v_one_x3f_4122_; lean_object* v_leFn_x3f_4123_; lean_object* v_ltFn_x3f_4124_; lean_object* v_addFn_4125_; lean_object* v_zsmulFn_4126_; lean_object* v_nsmulFn_4127_; lean_object* v_zsmulFn_x3f_4128_; lean_object* v_nsmulFn_x3f_4129_; lean_object* v_homomulFn_x3f_4130_; lean_object* v_subFn_4131_; lean_object* v_negFn_4132_; lean_object* v_vars_4133_; lean_object* v_varMap_4134_; lean_object* v_lowers_4135_; lean_object* v_uppers_4136_; lean_object* v_diseqs_4137_; lean_object* v_assignment_4138_; uint8_t v_caseSplits_4139_; lean_object* v_conflict_x3f_4140_; lean_object* v_diseqSplits_4141_; lean_object* v_elimEqs_4142_; lean_object* v_elimStack_4143_; lean_object* v_occurs_4144_; lean_object* v_ignored_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4160_; 
v_v_4102_ = lean_array_fget(v_structs_4089_, v_a_4086_);
v_id_4103_ = lean_ctor_get(v_v_4102_, 0);
v_ringId_x3f_4104_ = lean_ctor_get(v_v_4102_, 1);
v_type_4105_ = lean_ctor_get(v_v_4102_, 2);
v_u_4106_ = lean_ctor_get(v_v_4102_, 3);
v_intModuleInst_4107_ = lean_ctor_get(v_v_4102_, 4);
v_leInst_x3f_4108_ = lean_ctor_get(v_v_4102_, 5);
v_ltInst_x3f_4109_ = lean_ctor_get(v_v_4102_, 6);
v_lawfulOrderLTInst_x3f_4110_ = lean_ctor_get(v_v_4102_, 7);
v_isPreorderInst_x3f_4111_ = lean_ctor_get(v_v_4102_, 8);
v_orderedAddInst_x3f_4112_ = lean_ctor_get(v_v_4102_, 9);
v_isLinearInst_x3f_4113_ = lean_ctor_get(v_v_4102_, 10);
v_noNatDivInst_x3f_4114_ = lean_ctor_get(v_v_4102_, 11);
v_ringInst_x3f_4115_ = lean_ctor_get(v_v_4102_, 12);
v_commRingInst_x3f_4116_ = lean_ctor_get(v_v_4102_, 13);
v_orderedRingInst_x3f_4117_ = lean_ctor_get(v_v_4102_, 14);
v_fieldInst_x3f_4118_ = lean_ctor_get(v_v_4102_, 15);
v_charInst_x3f_4119_ = lean_ctor_get(v_v_4102_, 16);
v_zero_4120_ = lean_ctor_get(v_v_4102_, 17);
v_ofNatZero_4121_ = lean_ctor_get(v_v_4102_, 18);
v_one_x3f_4122_ = lean_ctor_get(v_v_4102_, 19);
v_leFn_x3f_4123_ = lean_ctor_get(v_v_4102_, 20);
v_ltFn_x3f_4124_ = lean_ctor_get(v_v_4102_, 21);
v_addFn_4125_ = lean_ctor_get(v_v_4102_, 22);
v_zsmulFn_4126_ = lean_ctor_get(v_v_4102_, 23);
v_nsmulFn_4127_ = lean_ctor_get(v_v_4102_, 24);
v_zsmulFn_x3f_4128_ = lean_ctor_get(v_v_4102_, 25);
v_nsmulFn_x3f_4129_ = lean_ctor_get(v_v_4102_, 26);
v_homomulFn_x3f_4130_ = lean_ctor_get(v_v_4102_, 27);
v_subFn_4131_ = lean_ctor_get(v_v_4102_, 28);
v_negFn_4132_ = lean_ctor_get(v_v_4102_, 29);
v_vars_4133_ = lean_ctor_get(v_v_4102_, 30);
v_varMap_4134_ = lean_ctor_get(v_v_4102_, 31);
v_lowers_4135_ = lean_ctor_get(v_v_4102_, 32);
v_uppers_4136_ = lean_ctor_get(v_v_4102_, 33);
v_diseqs_4137_ = lean_ctor_get(v_v_4102_, 34);
v_assignment_4138_ = lean_ctor_get(v_v_4102_, 35);
v_caseSplits_4139_ = lean_ctor_get_uint8(v_v_4102_, sizeof(void*)*42);
v_conflict_x3f_4140_ = lean_ctor_get(v_v_4102_, 36);
v_diseqSplits_4141_ = lean_ctor_get(v_v_4102_, 37);
v_elimEqs_4142_ = lean_ctor_get(v_v_4102_, 38);
v_elimStack_4143_ = lean_ctor_get(v_v_4102_, 39);
v_occurs_4144_ = lean_ctor_get(v_v_4102_, 40);
v_ignored_4145_ = lean_ctor_get(v_v_4102_, 41);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_v_4102_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4147_ = v_v_4102_;
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_ignored_4145_);
lean_inc(v_occurs_4144_);
lean_inc(v_elimStack_4143_);
lean_inc(v_elimEqs_4142_);
lean_inc(v_diseqSplits_4141_);
lean_inc(v_conflict_x3f_4140_);
lean_inc(v_assignment_4138_);
lean_inc(v_diseqs_4137_);
lean_inc(v_uppers_4136_);
lean_inc(v_lowers_4135_);
lean_inc(v_varMap_4134_);
lean_inc(v_vars_4133_);
lean_inc(v_negFn_4132_);
lean_inc(v_subFn_4131_);
lean_inc(v_homomulFn_x3f_4130_);
lean_inc(v_nsmulFn_x3f_4129_);
lean_inc(v_zsmulFn_x3f_4128_);
lean_inc(v_nsmulFn_4127_);
lean_inc(v_zsmulFn_4126_);
lean_inc(v_addFn_4125_);
lean_inc(v_ltFn_x3f_4124_);
lean_inc(v_leFn_x3f_4123_);
lean_inc(v_one_x3f_4122_);
lean_inc(v_ofNatZero_4121_);
lean_inc(v_zero_4120_);
lean_inc(v_charInst_x3f_4119_);
lean_inc(v_fieldInst_x3f_4118_);
lean_inc(v_orderedRingInst_x3f_4117_);
lean_inc(v_commRingInst_x3f_4116_);
lean_inc(v_ringInst_x3f_4115_);
lean_inc(v_noNatDivInst_x3f_4114_);
lean_inc(v_isLinearInst_x3f_4113_);
lean_inc(v_orderedAddInst_x3f_4112_);
lean_inc(v_isPreorderInst_x3f_4111_);
lean_inc(v_lawfulOrderLTInst_x3f_4110_);
lean_inc(v_ltInst_x3f_4109_);
lean_inc(v_leInst_x3f_4108_);
lean_inc(v_intModuleInst_4107_);
lean_inc(v_u_4106_);
lean_inc(v_type_4105_);
lean_inc(v_ringId_x3f_4104_);
lean_inc(v_id_4103_);
lean_dec(v_v_4102_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v_xs_x27_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4154_; 
v___x_4149_ = lean_box(0);
v_xs_x27_4150_ = lean_array_fset(v_structs_4089_, v_a_4086_, v___x_4149_);
v___x_4151_ = lean_box(1);
v___x_4152_ = l_Lean_PersistentArray_set___redArg(v_occurs_4144_, v_x_4087_, v___x_4151_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 40, v___x_4152_);
v___x_4154_ = v___x_4147_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_id_4103_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_ringId_x3f_4104_);
lean_ctor_set(v_reuseFailAlloc_4159_, 2, v_type_4105_);
lean_ctor_set(v_reuseFailAlloc_4159_, 3, v_u_4106_);
lean_ctor_set(v_reuseFailAlloc_4159_, 4, v_intModuleInst_4107_);
lean_ctor_set(v_reuseFailAlloc_4159_, 5, v_leInst_x3f_4108_);
lean_ctor_set(v_reuseFailAlloc_4159_, 6, v_ltInst_x3f_4109_);
lean_ctor_set(v_reuseFailAlloc_4159_, 7, v_lawfulOrderLTInst_x3f_4110_);
lean_ctor_set(v_reuseFailAlloc_4159_, 8, v_isPreorderInst_x3f_4111_);
lean_ctor_set(v_reuseFailAlloc_4159_, 9, v_orderedAddInst_x3f_4112_);
lean_ctor_set(v_reuseFailAlloc_4159_, 10, v_isLinearInst_x3f_4113_);
lean_ctor_set(v_reuseFailAlloc_4159_, 11, v_noNatDivInst_x3f_4114_);
lean_ctor_set(v_reuseFailAlloc_4159_, 12, v_ringInst_x3f_4115_);
lean_ctor_set(v_reuseFailAlloc_4159_, 13, v_commRingInst_x3f_4116_);
lean_ctor_set(v_reuseFailAlloc_4159_, 14, v_orderedRingInst_x3f_4117_);
lean_ctor_set(v_reuseFailAlloc_4159_, 15, v_fieldInst_x3f_4118_);
lean_ctor_set(v_reuseFailAlloc_4159_, 16, v_charInst_x3f_4119_);
lean_ctor_set(v_reuseFailAlloc_4159_, 17, v_zero_4120_);
lean_ctor_set(v_reuseFailAlloc_4159_, 18, v_ofNatZero_4121_);
lean_ctor_set(v_reuseFailAlloc_4159_, 19, v_one_x3f_4122_);
lean_ctor_set(v_reuseFailAlloc_4159_, 20, v_leFn_x3f_4123_);
lean_ctor_set(v_reuseFailAlloc_4159_, 21, v_ltFn_x3f_4124_);
lean_ctor_set(v_reuseFailAlloc_4159_, 22, v_addFn_4125_);
lean_ctor_set(v_reuseFailAlloc_4159_, 23, v_zsmulFn_4126_);
lean_ctor_set(v_reuseFailAlloc_4159_, 24, v_nsmulFn_4127_);
lean_ctor_set(v_reuseFailAlloc_4159_, 25, v_zsmulFn_x3f_4128_);
lean_ctor_set(v_reuseFailAlloc_4159_, 26, v_nsmulFn_x3f_4129_);
lean_ctor_set(v_reuseFailAlloc_4159_, 27, v_homomulFn_x3f_4130_);
lean_ctor_set(v_reuseFailAlloc_4159_, 28, v_subFn_4131_);
lean_ctor_set(v_reuseFailAlloc_4159_, 29, v_negFn_4132_);
lean_ctor_set(v_reuseFailAlloc_4159_, 30, v_vars_4133_);
lean_ctor_set(v_reuseFailAlloc_4159_, 31, v_varMap_4134_);
lean_ctor_set(v_reuseFailAlloc_4159_, 32, v_lowers_4135_);
lean_ctor_set(v_reuseFailAlloc_4159_, 33, v_uppers_4136_);
lean_ctor_set(v_reuseFailAlloc_4159_, 34, v_diseqs_4137_);
lean_ctor_set(v_reuseFailAlloc_4159_, 35, v_assignment_4138_);
lean_ctor_set(v_reuseFailAlloc_4159_, 36, v_conflict_x3f_4140_);
lean_ctor_set(v_reuseFailAlloc_4159_, 37, v_diseqSplits_4141_);
lean_ctor_set(v_reuseFailAlloc_4159_, 38, v_elimEqs_4142_);
lean_ctor_set(v_reuseFailAlloc_4159_, 39, v_elimStack_4143_);
lean_ctor_set(v_reuseFailAlloc_4159_, 40, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4159_, 41, v_ignored_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4159_, sizeof(void*)*42, v_caseSplits_4139_);
v___x_4154_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4155_ = lean_array_fset(v_xs_x27_4150_, v_a_4086_, v___x_4154_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4155_);
v___x_4157_ = v___x_4100_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_typeIdOf_4090_);
lean_ctor_set(v_reuseFailAlloc_4158_, 2, v_exprToStructId_4091_);
lean_ctor_set(v_reuseFailAlloc_4158_, 3, v_exprToStructIdEntries_4092_);
lean_ctor_set(v_reuseFailAlloc_4158_, 4, v_forbiddenNatModules_4093_);
lean_ctor_set(v_reuseFailAlloc_4158_, 5, v_natStructs_4094_);
lean_ctor_set(v_reuseFailAlloc_4158_, 6, v_natTypeIdOf_4095_);
lean_ctor_set(v_reuseFailAlloc_4158_, 7, v_exprToNatStructId_4096_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4170_, lean_object* v_x_4171_, lean_object* v_s_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4170_, v_x_4171_, v_s_4172_);
lean_dec(v_x_4171_);
lean_dec(v_a_4170_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4174_, lean_object* v_x_4175_, lean_object* v_c_4176_, lean_object* v_init_4177_, lean_object* v_x_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
if (lean_obj_tag(v_x_4178_) == 0)
{
lean_object* v_k_4191_; lean_object* v_l_4192_; lean_object* v_r_4193_; lean_object* v___x_4194_; 
v_k_4191_ = lean_ctor_get(v_x_4178_, 1);
lean_inc(v_k_4191_);
v_l_4192_ = lean_ctor_get(v_x_4178_, 3);
lean_inc(v_l_4192_);
v_r_4193_ = lean_ctor_get(v_x_4178_, 4);
lean_inc(v_r_4193_);
lean_dec_ref(v_x_4178_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
lean_inc(v___y_4183_);
lean_inc_ref(v___y_4182_);
lean_inc(v___y_4181_);
lean_inc(v___y_4180_);
lean_inc(v___y_4179_);
lean_inc_ref(v_c_4176_);
lean_inc(v_x_4175_);
lean_inc(v_a_4174_);
v___x_4194_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4174_, v_x_4175_, v_c_4176_, v_init_4177_, v_l_4192_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v___x_4195_; 
lean_dec_ref(v___x_4194_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
lean_inc(v___y_4183_);
lean_inc_ref(v___y_4182_);
lean_inc(v___y_4181_);
lean_inc(v___y_4180_);
lean_inc(v___y_4179_);
lean_inc_ref(v_c_4176_);
lean_inc(v_x_4175_);
lean_inc(v_a_4174_);
v___x_4195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4174_, v_x_4175_, v_c_4176_, v_k_4191_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v___x_4196_; 
lean_dec_ref(v___x_4195_);
v___x_4196_ = lean_box(0);
v_init_4177_ = v___x_4196_;
v_x_4178_ = v_r_4193_;
goto _start;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_r_4193_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v_c_4176_);
lean_dec(v_x_4175_);
lean_dec(v_a_4174_);
v_a_4198_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4195_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4195_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_dec(v_r_4193_);
lean_dec(v_k_4191_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v_c_4176_);
lean_dec(v_x_4175_);
lean_dec(v_a_4174_);
return v___x_4194_;
}
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v_c_4176_);
lean_dec(v_x_4175_);
lean_dec(v_a_4174_);
v___x_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_init_4177_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4208_ = _args[0];
lean_object* v_x_4209_ = _args[1];
lean_object* v_c_4210_ = _args[2];
lean_object* v_init_4211_ = _args[3];
lean_object* v_x_4212_ = _args[4];
lean_object* v___y_4213_ = _args[5];
lean_object* v___y_4214_ = _args[6];
lean_object* v___y_4215_ = _args[7];
lean_object* v___y_4216_ = _args[8];
lean_object* v___y_4217_ = _args[9];
lean_object* v___y_4218_ = _args[10];
lean_object* v___y_4219_ = _args[11];
lean_object* v___y_4220_ = _args[12];
lean_object* v___y_4221_ = _args[13];
lean_object* v___y_4222_ = _args[14];
lean_object* v___y_4223_ = _args[15];
lean_object* v___y_4224_ = _args[16];
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4208_, v_x_4209_, v_c_4210_, v_init_4211_, v_x_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4226_, lean_object* v_x_4227_, lean_object* v_c_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v_occurs_4243_; lean_object* v_size_4244_; lean_object* v___f_4245_; lean_object* v___y_4247_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4241_);
v_occurs_4243_ = lean_ctor_get(v_a_4242_, 40);
lean_inc_ref(v_occurs_4243_);
lean_dec(v_a_4242_);
v_size_4244_ = lean_ctor_get(v_occurs_4243_, 2);
lean_inc(v_x_4227_);
lean_inc(v_a_4229_);
v___f_4245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4245_, 0, v_a_4229_);
lean_closure_set(v___f_4245_, 1, v_x_4227_);
v___x_4269_ = lean_box(1);
v___x_4270_ = lean_nat_dec_lt(v_x_4227_, v_size_4244_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
lean_dec_ref(v_occurs_4243_);
v___x_4271_ = l_outOfBounds___redArg(v___x_4269_);
v___y_4247_ = v___x_4271_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4269_, v_occurs_4243_, v_x_4227_);
v___y_4247_ = v___x_4272_;
goto v___jp_4246_;
}
v___jp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4249_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4248_, v___f_4245_, v_a_4230_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___x_4250_; 
lean_dec_ref(v___x_4249_);
lean_inc(v_a_4239_);
lean_inc_ref(v_a_4238_);
lean_inc(v_a_4237_);
lean_inc_ref(v_a_4236_);
lean_inc(v_a_4235_);
lean_inc_ref(v_a_4234_);
lean_inc(v_a_4233_);
lean_inc_ref(v_a_4232_);
lean_inc(v_a_4231_);
lean_inc(v_a_4230_);
lean_inc(v_a_4229_);
lean_inc_ref(v_c_4228_);
lean_inc_n(v_x_4227_, 2);
lean_inc(v_a_4226_);
v___x_4250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4226_, v_x_4227_, v_c_4228_, v_x_4227_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_dec_ref(v___x_4250_);
v___x_4251_ = lean_box(0);
v___x_4252_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4226_, v_x_4227_, v_c_4228_, v___x_4251_, v___y_4247_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; 
v_unused_4260_ = lean_ctor_get(v___x_4252_, 0);
lean_dec(v_unused_4260_);
v___x_4254_ = v___x_4252_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_dec(v___x_4252_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 0, v___x_4251_);
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4251_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
v_a_4261_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4252_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4252_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_dec(v___y_4247_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_c_4228_);
lean_dec(v_x_4227_);
lean_dec(v_a_4226_);
return v___x_4250_;
}
}
else
{
lean_dec(v___y_4247_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_c_4228_);
lean_dec(v_x_4227_);
lean_dec(v_a_4226_);
return v___x_4249_;
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_c_4228_);
lean_dec(v_x_4227_);
lean_dec(v_a_4226_);
v_a_4273_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4241_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4241_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4281_, lean_object* v_x_4282_, lean_object* v_c_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4281_, v_x_4282_, v_c_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_){
_start:
{
lean_object* v_p_4314_; 
v_p_4314_ = lean_ctor_get(v_c_4297_, 0);
if (lean_obj_tag(v_p_4314_) == 1)
{
lean_object* v_k_4315_; lean_object* v_v_4316_; lean_object* v_p_4317_; lean_object* v_y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___x_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v_k_4315_ = lean_ctor_get(v_p_4314_, 0);
v_v_4316_ = lean_ctor_get(v_p_4314_, 1);
v_p_4317_ = lean_ctor_get(v_p_4314_, 2);
v___x_4368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_4369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4370_ = lean_int_dec_eq(v_k_4315_, v___x_4369_);
if (v___x_4370_ == 0)
{
uint8_t v___x_4371_; 
v___x_4371_ = lean_int_dec_eq(v_k_4315_, v___x_4368_);
if (v___x_4371_ == 0)
{
goto v___jp_4310_;
}
else
{
if (lean_obj_tag(v_p_4317_) == 1)
{
lean_object* v_k_4372_; lean_object* v_v_4373_; lean_object* v_p_4374_; uint8_t v___x_4375_; 
v_k_4372_ = lean_ctor_get(v_p_4317_, 0);
v_v_4373_ = lean_ctor_get(v_p_4317_, 1);
v_p_4374_ = lean_ctor_get(v_p_4317_, 2);
v___x_4375_ = lean_int_dec_eq(v_k_4372_, v___x_4369_);
if (v___x_4375_ == 0)
{
goto v___jp_4310_;
}
else
{
if (lean_obj_tag(v_p_4374_) == 0)
{
v_y_4319_ = v_v_4373_;
v___y_4320_ = v_a_4298_;
v___y_4321_ = v_a_4299_;
v___y_4322_ = v_a_4300_;
v___y_4323_ = v_a_4301_;
v___y_4324_ = v_a_4302_;
v___y_4325_ = v_a_4303_;
v___y_4326_ = v_a_4304_;
v___y_4327_ = v_a_4305_;
v___y_4328_ = v_a_4306_;
v___y_4329_ = v_a_4307_;
v___y_4330_ = v_a_4308_;
goto v___jp_4318_;
}
else
{
goto v___jp_4310_;
}
}
}
else
{
goto v___jp_4310_;
}
}
}
else
{
if (lean_obj_tag(v_p_4317_) == 1)
{
lean_object* v_k_4376_; lean_object* v_v_4377_; lean_object* v_p_4378_; uint8_t v___x_4379_; 
v_k_4376_ = lean_ctor_get(v_p_4317_, 0);
v_v_4377_ = lean_ctor_get(v_p_4317_, 1);
v_p_4378_ = lean_ctor_get(v_p_4317_, 2);
v___x_4379_ = lean_int_dec_eq(v_k_4376_, v___x_4368_);
if (v___x_4379_ == 0)
{
goto v___jp_4310_;
}
else
{
if (lean_obj_tag(v_p_4378_) == 0)
{
v_y_4319_ = v_v_4377_;
v___y_4320_ = v_a_4298_;
v___y_4321_ = v_a_4299_;
v___y_4322_ = v_a_4300_;
v___y_4323_ = v_a_4301_;
v___y_4324_ = v_a_4302_;
v___y_4325_ = v_a_4303_;
v___y_4326_ = v_a_4304_;
v___y_4327_ = v_a_4305_;
v___y_4328_ = v_a_4306_;
v___y_4329_ = v_a_4307_;
v___y_4330_ = v_a_4308_;
goto v___jp_4318_;
}
else
{
goto v___jp_4310_;
}
}
}
else
{
goto v___jp_4310_;
}
}
v___jp_4318_:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4316_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref(v___x_4331_);
v___x_4333_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4332_, v_a_4334_, v___y_4321_);
lean_dec(v_a_4334_);
lean_dec(v_a_4332_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4351_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4351_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4351_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_unbox(v_a_4336_);
lean_dec(v_a_4336_);
if (v___x_4340_ == 0)
{
uint8_t v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4341_ = 1;
v___x_4342_ = lean_box(v___x_4341_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4342_);
v___x_4344_ = v___x_4338_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
else
{
uint8_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4346_ = 0;
v___x_4347_ = lean_box(v___x_4346_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4347_);
v___x_4349_ = v___x_4338_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
return v___x_4335_;
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v_a_4332_);
v_a_4352_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4333_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4333_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4331_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4331_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
else
{
goto v___jp_4310_;
}
v___jp_4310_:
{
uint8_t v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = 0;
v___x_4312_ = lean_box(v___x_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_c_4380_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4394_){
_start:
{
lean_object* v_p_4396_; 
v_p_4396_ = lean_ctor_get(v_c_4394_, 0);
if (lean_obj_tag(v_p_4396_) == 1)
{
lean_object* v_k_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_k_4397_ = lean_ctor_get(v_p_4396_, 0);
v___x_4398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4399_ = lean_int_dec_lt(v_k_4397_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_c_4394_);
return v___x_4400_;
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4396_);
v___x_4402_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4396_, v___x_4401_);
v___x_4403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4403_, 0, v_c_4394_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
else
{
lean_object* v___x_4406_; 
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v_c_4394_);
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4410_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
lean_dec(v_a_4429_);
lean_dec_ref(v_a_4428_);
lean_dec(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec(v_a_4425_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4438_, lean_object* v_snd_4439_, lean_object* v_fst_4440_, lean_object* v_s_4441_){
_start:
{
lean_object* v_structs_4442_; lean_object* v_typeIdOf_4443_; lean_object* v_exprToStructId_4444_; lean_object* v_exprToStructIdEntries_4445_; lean_object* v_forbiddenNatModules_4446_; lean_object* v_natStructs_4447_; lean_object* v_natTypeIdOf_4448_; lean_object* v_exprToNatStructId_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; 
v_structs_4442_ = lean_ctor_get(v_s_4441_, 0);
v_typeIdOf_4443_ = lean_ctor_get(v_s_4441_, 1);
v_exprToStructId_4444_ = lean_ctor_get(v_s_4441_, 2);
v_exprToStructIdEntries_4445_ = lean_ctor_get(v_s_4441_, 3);
v_forbiddenNatModules_4446_ = lean_ctor_get(v_s_4441_, 4);
v_natStructs_4447_ = lean_ctor_get(v_s_4441_, 5);
v_natTypeIdOf_4448_ = lean_ctor_get(v_s_4441_, 6);
v_exprToNatStructId_4449_ = lean_ctor_get(v_s_4441_, 7);
v___x_4450_ = lean_array_get_size(v_structs_4442_);
v___x_4451_ = lean_nat_dec_lt(v___y_4438_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_dec(v_fst_4440_);
lean_dec_ref(v_snd_4439_);
return v_s_4441_;
}
else
{
lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4515_; 
lean_inc_ref(v_exprToNatStructId_4449_);
lean_inc_ref(v_natTypeIdOf_4448_);
lean_inc_ref(v_natStructs_4447_);
lean_inc_ref(v_forbiddenNatModules_4446_);
lean_inc_ref(v_exprToStructIdEntries_4445_);
lean_inc_ref(v_exprToStructId_4444_);
lean_inc_ref(v_typeIdOf_4443_);
lean_inc_ref(v_structs_4442_);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_s_4441_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; lean_object* v_unused_4517_; lean_object* v_unused_4518_; lean_object* v_unused_4519_; lean_object* v_unused_4520_; lean_object* v_unused_4521_; lean_object* v_unused_4522_; lean_object* v_unused_4523_; 
v_unused_4516_ = lean_ctor_get(v_s_4441_, 7);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v_s_4441_, 6);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_s_4441_, 5);
lean_dec(v_unused_4518_);
v_unused_4519_ = lean_ctor_get(v_s_4441_, 4);
lean_dec(v_unused_4519_);
v_unused_4520_ = lean_ctor_get(v_s_4441_, 3);
lean_dec(v_unused_4520_);
v_unused_4521_ = lean_ctor_get(v_s_4441_, 2);
lean_dec(v_unused_4521_);
v_unused_4522_ = lean_ctor_get(v_s_4441_, 1);
lean_dec(v_unused_4522_);
v_unused_4523_ = lean_ctor_get(v_s_4441_, 0);
lean_dec(v_unused_4523_);
v___x_4453_ = v_s_4441_;
v_isShared_4454_ = v_isSharedCheck_4515_;
goto v_resetjp_4452_;
}
else
{
lean_dec(v_s_4441_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4515_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v_v_4455_; lean_object* v_id_4456_; lean_object* v_ringId_x3f_4457_; lean_object* v_type_4458_; lean_object* v_u_4459_; lean_object* v_intModuleInst_4460_; lean_object* v_leInst_x3f_4461_; lean_object* v_ltInst_x3f_4462_; lean_object* v_lawfulOrderLTInst_x3f_4463_; lean_object* v_isPreorderInst_x3f_4464_; lean_object* v_orderedAddInst_x3f_4465_; lean_object* v_isLinearInst_x3f_4466_; lean_object* v_noNatDivInst_x3f_4467_; lean_object* v_ringInst_x3f_4468_; lean_object* v_commRingInst_x3f_4469_; lean_object* v_orderedRingInst_x3f_4470_; lean_object* v_fieldInst_x3f_4471_; lean_object* v_charInst_x3f_4472_; lean_object* v_zero_4473_; lean_object* v_ofNatZero_4474_; lean_object* v_one_x3f_4475_; lean_object* v_leFn_x3f_4476_; lean_object* v_ltFn_x3f_4477_; lean_object* v_addFn_4478_; lean_object* v_zsmulFn_4479_; lean_object* v_nsmulFn_4480_; lean_object* v_zsmulFn_x3f_4481_; lean_object* v_nsmulFn_x3f_4482_; lean_object* v_homomulFn_x3f_4483_; lean_object* v_subFn_4484_; lean_object* v_negFn_4485_; lean_object* v_vars_4486_; lean_object* v_varMap_4487_; lean_object* v_lowers_4488_; lean_object* v_uppers_4489_; lean_object* v_diseqs_4490_; lean_object* v_assignment_4491_; uint8_t v_caseSplits_4492_; lean_object* v_conflict_x3f_4493_; lean_object* v_diseqSplits_4494_; lean_object* v_elimEqs_4495_; lean_object* v_elimStack_4496_; lean_object* v_occurs_4497_; lean_object* v_ignored_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4514_; 
v_v_4455_ = lean_array_fget(v_structs_4442_, v___y_4438_);
v_id_4456_ = lean_ctor_get(v_v_4455_, 0);
v_ringId_x3f_4457_ = lean_ctor_get(v_v_4455_, 1);
v_type_4458_ = lean_ctor_get(v_v_4455_, 2);
v_u_4459_ = lean_ctor_get(v_v_4455_, 3);
v_intModuleInst_4460_ = lean_ctor_get(v_v_4455_, 4);
v_leInst_x3f_4461_ = lean_ctor_get(v_v_4455_, 5);
v_ltInst_x3f_4462_ = lean_ctor_get(v_v_4455_, 6);
v_lawfulOrderLTInst_x3f_4463_ = lean_ctor_get(v_v_4455_, 7);
v_isPreorderInst_x3f_4464_ = lean_ctor_get(v_v_4455_, 8);
v_orderedAddInst_x3f_4465_ = lean_ctor_get(v_v_4455_, 9);
v_isLinearInst_x3f_4466_ = lean_ctor_get(v_v_4455_, 10);
v_noNatDivInst_x3f_4467_ = lean_ctor_get(v_v_4455_, 11);
v_ringInst_x3f_4468_ = lean_ctor_get(v_v_4455_, 12);
v_commRingInst_x3f_4469_ = lean_ctor_get(v_v_4455_, 13);
v_orderedRingInst_x3f_4470_ = lean_ctor_get(v_v_4455_, 14);
v_fieldInst_x3f_4471_ = lean_ctor_get(v_v_4455_, 15);
v_charInst_x3f_4472_ = lean_ctor_get(v_v_4455_, 16);
v_zero_4473_ = lean_ctor_get(v_v_4455_, 17);
v_ofNatZero_4474_ = lean_ctor_get(v_v_4455_, 18);
v_one_x3f_4475_ = lean_ctor_get(v_v_4455_, 19);
v_leFn_x3f_4476_ = lean_ctor_get(v_v_4455_, 20);
v_ltFn_x3f_4477_ = lean_ctor_get(v_v_4455_, 21);
v_addFn_4478_ = lean_ctor_get(v_v_4455_, 22);
v_zsmulFn_4479_ = lean_ctor_get(v_v_4455_, 23);
v_nsmulFn_4480_ = lean_ctor_get(v_v_4455_, 24);
v_zsmulFn_x3f_4481_ = lean_ctor_get(v_v_4455_, 25);
v_nsmulFn_x3f_4482_ = lean_ctor_get(v_v_4455_, 26);
v_homomulFn_x3f_4483_ = lean_ctor_get(v_v_4455_, 27);
v_subFn_4484_ = lean_ctor_get(v_v_4455_, 28);
v_negFn_4485_ = lean_ctor_get(v_v_4455_, 29);
v_vars_4486_ = lean_ctor_get(v_v_4455_, 30);
v_varMap_4487_ = lean_ctor_get(v_v_4455_, 31);
v_lowers_4488_ = lean_ctor_get(v_v_4455_, 32);
v_uppers_4489_ = lean_ctor_get(v_v_4455_, 33);
v_diseqs_4490_ = lean_ctor_get(v_v_4455_, 34);
v_assignment_4491_ = lean_ctor_get(v_v_4455_, 35);
v_caseSplits_4492_ = lean_ctor_get_uint8(v_v_4455_, sizeof(void*)*42);
v_conflict_x3f_4493_ = lean_ctor_get(v_v_4455_, 36);
v_diseqSplits_4494_ = lean_ctor_get(v_v_4455_, 37);
v_elimEqs_4495_ = lean_ctor_get(v_v_4455_, 38);
v_elimStack_4496_ = lean_ctor_get(v_v_4455_, 39);
v_occurs_4497_ = lean_ctor_get(v_v_4455_, 40);
v_ignored_4498_ = lean_ctor_get(v_v_4455_, 41);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_v_4455_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4500_ = v_v_4455_;
v_isShared_4501_ = v_isSharedCheck_4514_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_ignored_4498_);
lean_inc(v_occurs_4497_);
lean_inc(v_elimStack_4496_);
lean_inc(v_elimEqs_4495_);
lean_inc(v_diseqSplits_4494_);
lean_inc(v_conflict_x3f_4493_);
lean_inc(v_assignment_4491_);
lean_inc(v_diseqs_4490_);
lean_inc(v_uppers_4489_);
lean_inc(v_lowers_4488_);
lean_inc(v_varMap_4487_);
lean_inc(v_vars_4486_);
lean_inc(v_negFn_4485_);
lean_inc(v_subFn_4484_);
lean_inc(v_homomulFn_x3f_4483_);
lean_inc(v_nsmulFn_x3f_4482_);
lean_inc(v_zsmulFn_x3f_4481_);
lean_inc(v_nsmulFn_4480_);
lean_inc(v_zsmulFn_4479_);
lean_inc(v_addFn_4478_);
lean_inc(v_ltFn_x3f_4477_);
lean_inc(v_leFn_x3f_4476_);
lean_inc(v_one_x3f_4475_);
lean_inc(v_ofNatZero_4474_);
lean_inc(v_zero_4473_);
lean_inc(v_charInst_x3f_4472_);
lean_inc(v_fieldInst_x3f_4471_);
lean_inc(v_orderedRingInst_x3f_4470_);
lean_inc(v_commRingInst_x3f_4469_);
lean_inc(v_ringInst_x3f_4468_);
lean_inc(v_noNatDivInst_x3f_4467_);
lean_inc(v_isLinearInst_x3f_4466_);
lean_inc(v_orderedAddInst_x3f_4465_);
lean_inc(v_isPreorderInst_x3f_4464_);
lean_inc(v_lawfulOrderLTInst_x3f_4463_);
lean_inc(v_ltInst_x3f_4462_);
lean_inc(v_leInst_x3f_4461_);
lean_inc(v_intModuleInst_4460_);
lean_inc(v_u_4459_);
lean_inc(v_type_4458_);
lean_inc(v_ringId_x3f_4457_);
lean_inc(v_id_4456_);
lean_dec(v_v_4455_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4514_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v_xs_x27_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4502_ = lean_box(0);
v_xs_x27_4503_ = lean_array_fset(v_structs_4442_, v___y_4438_, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v_snd_4439_);
v___x_4505_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4495_, v_fst_4440_, v___x_4504_);
v___x_4506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4506_, 0, v_fst_4440_);
lean_ctor_set(v___x_4506_, 1, v_elimStack_4496_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 39, v___x_4506_);
lean_ctor_set(v___x_4500_, 38, v___x_4505_);
v___x_4508_ = v___x_4500_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_id_4456_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_ringId_x3f_4457_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_type_4458_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_u_4459_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v_intModuleInst_4460_);
lean_ctor_set(v_reuseFailAlloc_4513_, 5, v_leInst_x3f_4461_);
lean_ctor_set(v_reuseFailAlloc_4513_, 6, v_ltInst_x3f_4462_);
lean_ctor_set(v_reuseFailAlloc_4513_, 7, v_lawfulOrderLTInst_x3f_4463_);
lean_ctor_set(v_reuseFailAlloc_4513_, 8, v_isPreorderInst_x3f_4464_);
lean_ctor_set(v_reuseFailAlloc_4513_, 9, v_orderedAddInst_x3f_4465_);
lean_ctor_set(v_reuseFailAlloc_4513_, 10, v_isLinearInst_x3f_4466_);
lean_ctor_set(v_reuseFailAlloc_4513_, 11, v_noNatDivInst_x3f_4467_);
lean_ctor_set(v_reuseFailAlloc_4513_, 12, v_ringInst_x3f_4468_);
lean_ctor_set(v_reuseFailAlloc_4513_, 13, v_commRingInst_x3f_4469_);
lean_ctor_set(v_reuseFailAlloc_4513_, 14, v_orderedRingInst_x3f_4470_);
lean_ctor_set(v_reuseFailAlloc_4513_, 15, v_fieldInst_x3f_4471_);
lean_ctor_set(v_reuseFailAlloc_4513_, 16, v_charInst_x3f_4472_);
lean_ctor_set(v_reuseFailAlloc_4513_, 17, v_zero_4473_);
lean_ctor_set(v_reuseFailAlloc_4513_, 18, v_ofNatZero_4474_);
lean_ctor_set(v_reuseFailAlloc_4513_, 19, v_one_x3f_4475_);
lean_ctor_set(v_reuseFailAlloc_4513_, 20, v_leFn_x3f_4476_);
lean_ctor_set(v_reuseFailAlloc_4513_, 21, v_ltFn_x3f_4477_);
lean_ctor_set(v_reuseFailAlloc_4513_, 22, v_addFn_4478_);
lean_ctor_set(v_reuseFailAlloc_4513_, 23, v_zsmulFn_4479_);
lean_ctor_set(v_reuseFailAlloc_4513_, 24, v_nsmulFn_4480_);
lean_ctor_set(v_reuseFailAlloc_4513_, 25, v_zsmulFn_x3f_4481_);
lean_ctor_set(v_reuseFailAlloc_4513_, 26, v_nsmulFn_x3f_4482_);
lean_ctor_set(v_reuseFailAlloc_4513_, 27, v_homomulFn_x3f_4483_);
lean_ctor_set(v_reuseFailAlloc_4513_, 28, v_subFn_4484_);
lean_ctor_set(v_reuseFailAlloc_4513_, 29, v_negFn_4485_);
lean_ctor_set(v_reuseFailAlloc_4513_, 30, v_vars_4486_);
lean_ctor_set(v_reuseFailAlloc_4513_, 31, v_varMap_4487_);
lean_ctor_set(v_reuseFailAlloc_4513_, 32, v_lowers_4488_);
lean_ctor_set(v_reuseFailAlloc_4513_, 33, v_uppers_4489_);
lean_ctor_set(v_reuseFailAlloc_4513_, 34, v_diseqs_4490_);
lean_ctor_set(v_reuseFailAlloc_4513_, 35, v_assignment_4491_);
lean_ctor_set(v_reuseFailAlloc_4513_, 36, v_conflict_x3f_4493_);
lean_ctor_set(v_reuseFailAlloc_4513_, 37, v_diseqSplits_4494_);
lean_ctor_set(v_reuseFailAlloc_4513_, 38, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4513_, 39, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4513_, 40, v_occurs_4497_);
lean_ctor_set(v_reuseFailAlloc_4513_, 41, v_ignored_4498_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*42, v_caseSplits_4492_);
v___x_4508_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; lean_object* v___x_4511_; 
v___x_4509_ = lean_array_fset(v_xs_x27_4503_, v___y_4438_, v___x_4508_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4509_);
v___x_4511_ = v___x_4453_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4509_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_typeIdOf_4443_);
lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_exprToStructId_4444_);
lean_ctor_set(v_reuseFailAlloc_4512_, 3, v_exprToStructIdEntries_4445_);
lean_ctor_set(v_reuseFailAlloc_4512_, 4, v_forbiddenNatModules_4446_);
lean_ctor_set(v_reuseFailAlloc_4512_, 5, v_natStructs_4447_);
lean_ctor_set(v_reuseFailAlloc_4512_, 6, v_natTypeIdOf_4448_);
lean_ctor_set(v_reuseFailAlloc_4512_, 7, v_exprToNatStructId_4449_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4524_, lean_object* v_snd_4525_, lean_object* v_fst_4526_, lean_object* v_s_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4524_, v_snd_4525_, v_fst_4526_, v_s_4527_);
lean_dec(v___y_4524_);
return v_res_4528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4531_ = l_Lean_stringToMessageData(v___x_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v_cls_4748_; lean_object* v___x_4749_; lean_object* v_a_4750_; uint8_t v___x_4751_; 
v_cls_4748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_4749_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4748_, v_a_4547_);
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_a_4750_);
lean_dec_ref(v___x_4749_);
v___x_4751_ = lean_unbox(v_a_4750_);
lean_dec(v_a_4750_);
if (v___x_4751_ == 0)
{
v___y_4650_ = v_a_4538_;
v___y_4651_ = v_a_4539_;
v___y_4652_ = v_a_4540_;
v___y_4653_ = v_a_4541_;
v___y_4654_ = v_a_4542_;
v___y_4655_ = v_a_4543_;
v___y_4656_ = v_a_4544_;
v___y_4657_ = v_a_4545_;
v___y_4658_ = v_a_4546_;
v___y_4659_ = v_a_4547_;
v___y_4660_ = v_a_4548_;
goto v___jp_4649_;
}
else
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4753_);
lean_dec_ref(v___x_4752_);
v___x_4754_ = l_Lean_MessageData_ofExpr(v_a_4753_);
v___x_4755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4748_, v___x_4754_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_dec_ref(v___x_4755_);
v___y_4650_ = v_a_4538_;
v___y_4651_ = v_a_4539_;
v___y_4652_ = v_a_4540_;
v___y_4653_ = v_a_4541_;
v___y_4654_ = v_a_4542_;
v___y_4655_ = v_a_4543_;
v___y_4656_ = v_a_4544_;
v___y_4657_ = v_a_4545_;
v___y_4658_ = v_a_4546_;
v___y_4659_ = v_a_4547_;
v___y_4660_ = v_a_4548_;
goto v___jp_4649_;
}
else
{
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_c_4537_);
return v___x_4755_;
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_c_4537_);
v_a_4756_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4752_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4752_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
v___jp_4550_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = lean_box(0);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
return v___x_4552_;
}
v___jp_4553_:
{
lean_object* v___f_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
lean_inc(v___y_4559_);
v___f_4570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4570_, 0, v___y_4559_);
lean_closure_set(v___f_4570_, 1, v___y_4555_);
lean_closure_set(v___f_4570_, 2, v___y_4554_);
v___x_4571_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4572_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4571_, v___f_4570_, v___y_4560_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v___x_4573_; 
lean_dec_ref(v___x_4572_);
v___x_4573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4558_, v___y_4556_, v___y_4557_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
return v___x_4573_;
}
else
{
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
return v___x_4572_;
}
}
v___jp_4574_:
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; uint8_t v_caseSplits_4593_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref(v___x_4591_);
v_caseSplits_4593_ = lean_ctor_get_uint8(v_a_4592_, sizeof(void*)*42);
lean_dec(v_a_4592_);
if (v_caseSplits_4593_ == 0)
{
lean_object* v___x_4594_; 
v___x_4594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4578_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; uint8_t v___x_4596_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v___x_4596_ = lean_unbox(v_a_4595_);
lean_dec(v_a_4595_);
if (v___x_4596_ == 0)
{
v___y_4554_ = v___y_4575_;
v___y_4555_ = v___y_4576_;
v___y_4556_ = v___y_4577_;
v___y_4557_ = v___y_4578_;
v___y_4558_ = v___y_4579_;
v___y_4559_ = v___y_4580_;
v___y_4560_ = v___y_4581_;
v___y_4561_ = v___y_4582_;
v___y_4562_ = v___y_4583_;
v___y_4563_ = v___y_4584_;
v___y_4564_ = v___y_4585_;
v___y_4565_ = v___y_4586_;
v___y_4566_ = v___y_4587_;
v___y_4567_ = v___y_4588_;
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___y_4590_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4597_; lean_object* v_a_4598_; lean_object* v___x_4599_; 
lean_inc_ref(v___y_4578_);
v___x_4597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4578_);
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
lean_inc(v___y_4590_);
lean_inc_ref(v___y_4589_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc_ref(v___y_4585_);
lean_inc(v___y_4584_);
lean_inc_ref(v___y_4583_);
lean_inc(v___y_4582_);
lean_inc(v___y_4581_);
lean_inc(v___y_4580_);
v___x_4599_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4598_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_dec_ref(v___x_4599_);
v___y_4554_ = v___y_4575_;
v___y_4555_ = v___y_4576_;
v___y_4556_ = v___y_4577_;
v___y_4557_ = v___y_4578_;
v___y_4558_ = v___y_4579_;
v___y_4559_ = v___y_4580_;
v___y_4560_ = v___y_4581_;
v___y_4561_ = v___y_4582_;
v___y_4562_ = v___y_4583_;
v___y_4563_ = v___y_4584_;
v___y_4564_ = v___y_4585_;
v___y_4565_ = v___y_4586_;
v___y_4566_ = v___y_4587_;
v___y_4567_ = v___y_4588_;
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___y_4590_;
goto v___jp_4553_;
}
else
{
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
return v___x_4599_;
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
v_a_4600_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4594_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4594_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
else
{
v___y_4554_ = v___y_4575_;
v___y_4555_ = v___y_4576_;
v___y_4556_ = v___y_4577_;
v___y_4557_ = v___y_4578_;
v___y_4558_ = v___y_4579_;
v___y_4559_ = v___y_4580_;
v___y_4560_ = v___y_4581_;
v___y_4561_ = v___y_4582_;
v___y_4562_ = v___y_4583_;
v___y_4563_ = v___y_4584_;
v___y_4564_ = v___y_4585_;
v___y_4565_ = v___y_4586_;
v___y_4566_ = v___y_4587_;
v___y_4567_ = v___y_4588_;
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___y_4590_;
goto v___jp_4553_;
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
v_a_4608_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4591_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4591_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
v___jp_4616_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v_a_4635_; uint8_t v___x_4636_; 
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4634_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4633_, v___y_4631_);
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref(v___x_4634_);
v___x_4636_ = lean_unbox(v_a_4635_);
lean_dec(v_a_4635_);
if (v___x_4636_ == 0)
{
v___y_4575_ = v___y_4617_;
v___y_4576_ = v___y_4618_;
v___y_4577_ = v___y_4619_;
v___y_4578_ = v___y_4620_;
v___y_4579_ = v___y_4621_;
v___y_4580_ = v___y_4622_;
v___y_4581_ = v___y_4623_;
v___y_4582_ = v___y_4624_;
v___y_4583_ = v___y_4625_;
v___y_4584_ = v___y_4626_;
v___y_4585_ = v___y_4627_;
v___y_4586_ = v___y_4628_;
v___y_4587_ = v___y_4629_;
v___y_4588_ = v___y_4630_;
v___y_4589_ = v___y_4631_;
v___y_4590_ = v___y_4632_;
goto v___jp_4574_;
}
else
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v___y_4620_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref(v___x_4637_);
v___x_4639_ = l_Lean_MessageData_ofExpr(v_a_4638_);
v___x_4640_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4633_, v___x_4639_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_dec_ref(v___x_4640_);
v___y_4575_ = v___y_4617_;
v___y_4576_ = v___y_4618_;
v___y_4577_ = v___y_4619_;
v___y_4578_ = v___y_4620_;
v___y_4579_ = v___y_4621_;
v___y_4580_ = v___y_4622_;
v___y_4581_ = v___y_4623_;
v___y_4582_ = v___y_4624_;
v___y_4583_ = v___y_4625_;
v___y_4584_ = v___y_4626_;
v___y_4585_ = v___y_4627_;
v___y_4586_ = v___y_4628_;
v___y_4587_ = v___y_4629_;
v___y_4588_ = v___y_4630_;
v___y_4589_ = v___y_4631_;
v___y_4590_ = v___y_4632_;
goto v___jp_4574_;
}
else
{
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
return v___x_4640_;
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
v_a_4641_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4637_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4637_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
v___jp_4649_:
{
lean_object* v___x_4661_; 
lean_inc_ref(v___y_4659_);
v___x_4661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4537_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4661_) == 0)
{
lean_object* v_a_4662_; lean_object* v_p_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v_a_4662_ = lean_ctor_get(v___x_4661_, 0);
lean_inc(v_a_4662_);
lean_dec_ref(v___x_4661_);
v_p_4663_ = lean_ctor_get(v_a_4662_, 0);
v___x_4664_ = lean_box(0);
v___x_4665_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4663_, v___x_4664_);
if (v___x_4665_ == 0)
{
lean_object* v___x_4666_; 
lean_inc(v___y_4660_);
lean_inc_ref(v___y_4659_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
lean_inc(v___y_4654_);
lean_inc_ref(v___y_4653_);
lean_inc(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc(v___y_4650_);
v___x_4666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4662_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v_snd_4668_; lean_object* v_fst_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4715_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref(v___x_4666_);
v_snd_4668_ = lean_ctor_get(v_a_4667_, 1);
v_fst_4669_ = lean_ctor_get(v_a_4667_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_a_4667_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4671_ = v_a_4667_;
v_isShared_4672_ = v_isSharedCheck_4715_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_snd_4668_);
lean_inc(v_fst_4669_);
lean_dec(v_a_4667_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4715_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v_fst_4673_; lean_object* v_snd_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4714_; 
v_fst_4673_ = lean_ctor_get(v_snd_4668_, 0);
v_snd_4674_ = lean_ctor_get(v_snd_4668_, 1);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_snd_4668_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4676_ = v_snd_4668_;
v_isShared_4677_ = v_isSharedCheck_4714_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_snd_4674_);
lean_inc(v_fst_4673_);
lean_dec(v_snd_4668_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4714_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v_a_4680_; uint8_t v___x_4681_; 
v___x_4678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4679_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4678_, v___y_4659_);
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v___x_4679_);
v___x_4681_ = lean_unbox(v_a_4680_);
lean_dec(v_a_4680_);
if (v___x_4681_ == 0)
{
lean_del_object(v___x_4676_);
lean_del_object(v___x_4671_);
lean_inc(v_snd_4674_);
lean_inc(v_fst_4673_);
v___y_4617_ = v_fst_4673_;
v___y_4618_ = v_snd_4674_;
v___y_4619_ = v_fst_4673_;
v___y_4620_ = v_snd_4674_;
v___y_4621_ = v_fst_4669_;
v___y_4622_ = v___y_4650_;
v___y_4623_ = v___y_4651_;
v___y_4624_ = v___y_4652_;
v___y_4625_ = v___y_4653_;
v___y_4626_ = v___y_4654_;
v___y_4627_ = v___y_4655_;
v___y_4628_ = v___y_4656_;
v___y_4629_ = v___y_4657_;
v___y_4630_ = v___y_4658_;
v___y_4631_ = v___y_4659_;
v___y_4632_ = v___y_4660_;
goto v___jp_4616_;
}
else
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4673_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4684_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref(v___x_4682_);
v___x_4684_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_snd_4674_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref(v___x_4684_);
v___x_4686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4687_ = l_Lean_MessageData_ofExpr(v_a_4683_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set_tag(v___x_4676_, 7);
lean_ctor_set(v___x_4676_, 1, v___x_4687_);
lean_ctor_set(v___x_4676_, 0, v___x_4686_);
v___x_4689_ = v___x_4676_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 7);
lean_ctor_set(v___x_4671_, 1, v___x_4690_);
lean_ctor_set(v___x_4671_, 0, v___x_4689_);
v___x_4692_ = v___x_4671_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = l_Lean_MessageData_ofExpr(v_a_4685_);
v___x_4694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4692_);
lean_ctor_set(v___x_4694_, 1, v___x_4693_);
v___x_4695_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4678_, v___x_4694_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_dec_ref(v___x_4695_);
lean_inc(v_snd_4674_);
lean_inc(v_fst_4673_);
v___y_4617_ = v_fst_4673_;
v___y_4618_ = v_snd_4674_;
v___y_4619_ = v_fst_4673_;
v___y_4620_ = v_snd_4674_;
v___y_4621_ = v_fst_4669_;
v___y_4622_ = v___y_4650_;
v___y_4623_ = v___y_4651_;
v___y_4624_ = v___y_4652_;
v___y_4625_ = v___y_4653_;
v___y_4626_ = v___y_4654_;
v___y_4627_ = v___y_4655_;
v___y_4628_ = v___y_4656_;
v___y_4629_ = v___y_4657_;
v___y_4630_ = v___y_4658_;
v___y_4631_ = v___y_4659_;
v___y_4632_ = v___y_4660_;
goto v___jp_4616_;
}
else
{
lean_dec(v_snd_4674_);
lean_dec(v_fst_4673_);
lean_dec(v_fst_4669_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
return v___x_4695_;
}
}
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v_a_4683_);
lean_del_object(v___x_4676_);
lean_dec(v_snd_4674_);
lean_dec(v_fst_4673_);
lean_del_object(v___x_4671_);
lean_dec(v_fst_4669_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
v_a_4698_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4684_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4684_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
lean_del_object(v___x_4676_);
lean_dec(v_snd_4674_);
lean_dec(v_fst_4673_);
lean_del_object(v___x_4671_);
lean_dec(v_fst_4669_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
v_a_4706_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4682_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4682_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
v_a_4716_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v___x_4666_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4666_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
else
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v_a_4726_; uint8_t v___x_4727_; 
v___x_4724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4725_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4724_, v___y_4659_);
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
lean_inc(v_a_4726_);
lean_dec_ref(v___x_4725_);
v___x_4727_ = lean_unbox(v_a_4726_);
lean_dec(v_a_4726_);
if (v___x_4727_ == 0)
{
lean_dec(v_a_4662_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
goto v___jp_4550_;
}
else
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_a_4662_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec(v_a_4662_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref(v___x_4728_);
v___x_4730_ = l_Lean_MessageData_ofExpr(v_a_4729_);
v___x_4731_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4724_, v___x_4730_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_dec_ref(v___x_4731_);
goto v___jp_4550_;
}
else
{
return v___x_4731_;
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
v_a_4732_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4728_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4728_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___y_4650_);
v_a_4740_ = lean_ctor_get(v___x_4661_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4661_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4661_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4782_, lean_object* v_b_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_cls_4789_; lean_object* v___x_4790_; lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4806_; 
v_cls_4789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4790_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4789_, v_a_4786_);
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4806_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4806_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
uint8_t v___x_4795_; 
v___x_4795_ = lean_unbox(v_a_4791_);
lean_dec(v_a_4791_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; lean_object* v___x_4798_; 
lean_dec_ref(v_b_4783_);
lean_dec_ref(v_a_4782_);
v___x_4796_ = lean_box(0);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4796_);
v___x_4798_ = v___x_4793_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
lean_del_object(v___x_4793_);
v___x_4800_ = l_Lean_MessageData_ofExpr(v_a_4782_);
v___x_4801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_4802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4800_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
v___x_4803_ = l_Lean_MessageData_ofExpr(v_b_4783_);
v___x_4804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4802_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
v___x_4805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4789_, v___x_4804_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
return v___x_4805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4807_, lean_object* v_b_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4807_, v_b_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4815_, lean_object* v_b_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4815_, v_b_4816_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4830_, lean_object* v_b_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4830_, v_b_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec(v_a_4832_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4845_, lean_object* v_b_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4845_, v_a_4848_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; uint8_t v___x_4861_; lean_object* v___x_4862_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref(v___x_4859_);
v___x_4861_ = 0;
lean_inc(v_a_4857_);
lean_inc_ref(v_a_4856_);
lean_inc(v_a_4855_);
lean_inc_ref(v_a_4854_);
lean_inc(v_a_4853_);
lean_inc_ref(v_a_4852_);
lean_inc(v_a_4851_);
lean_inc_ref(v_a_4850_);
lean_inc(v_a_4849_);
lean_inc(v_a_4848_);
lean_inc(v_a_4847_);
lean_inc_ref(v_a_4845_);
v___x_4862_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4845_, v___x_4861_, v_a_4860_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4912_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4865_ = v___x_4862_;
v_isShared_4866_ = v_isSharedCheck_4912_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4862_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4912_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
if (lean_obj_tag(v_a_4863_) == 1)
{
lean_object* v_val_4867_; lean_object* v___x_4868_; 
lean_del_object(v___x_4865_);
v_val_4867_ = lean_ctor_get(v_a_4863_, 0);
lean_inc(v_val_4867_);
lean_dec_ref(v_a_4863_);
v___x_4868_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4846_, v_a_4848_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4870_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref(v___x_4868_);
lean_inc(v_a_4857_);
lean_inc_ref(v_a_4856_);
lean_inc(v_a_4855_);
lean_inc_ref(v_a_4854_);
lean_inc(v_a_4853_);
lean_inc_ref(v_a_4852_);
lean_inc(v_a_4851_);
lean_inc_ref(v_a_4850_);
lean_inc(v_a_4849_);
lean_inc(v_a_4848_);
lean_inc(v_a_4847_);
lean_inc_ref(v_b_4846_);
v___x_4870_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4846_, v___x_4861_, v_a_4869_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4891_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4891_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4891_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
if (lean_obj_tag(v_a_4871_) == 1)
{
lean_object* v_val_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v_val_4875_ = lean_ctor_get(v_a_4871_, 0);
lean_inc(v_val_4875_);
lean_dec_ref(v_a_4871_);
lean_inc(v_val_4875_);
lean_inc(v_val_4867_);
v___x_4876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4876_, 0, v_val_4867_);
lean_ctor_set(v___x_4876_, 1, v_val_4875_);
v___x_4877_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4876_);
v___x_4878_ = lean_box(0);
v___x_4879_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4877_, v___x_4878_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_del_object(v___x_4873_);
v___x_4880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4880_, 0, v_a_4845_);
lean_ctor_set(v___x_4880_, 1, v_b_4846_);
lean_ctor_set(v___x_4880_, 2, v_val_4867_);
lean_ctor_set(v___x_4880_, 3, v_val_4875_);
v___x_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4877_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4881_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
return v___x_4882_;
}
else
{
lean_object* v___x_4883_; lean_object* v___x_4885_; 
lean_dec(v___x_4877_);
lean_dec(v_val_4875_);
lean_dec(v_val_4867_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v___x_4883_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4883_);
v___x_4885_ = v___x_4873_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
lean_dec(v_a_4871_);
lean_dec(v_val_4867_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v___x_4887_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4887_);
v___x_4889_ = v___x_4873_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_val_4867_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v_a_4892_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4870_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4870_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec(v_val_4867_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v_a_4900_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4868_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4868_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_object* v___x_4908_; lean_object* v___x_4910_; 
lean_dec(v_a_4863_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v___x_4908_ = lean_box(0);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 0, v___x_4908_);
v___x_4910_ = v___x_4865_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v_a_4913_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4862_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4862_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_b_4846_);
lean_dec_ref(v_a_4845_);
v_a_4921_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4859_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4859_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4929_, lean_object* v_b_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4929_, v_b_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref(v___x_4958_);
lean_inc(v_a_4956_);
lean_inc_ref(v_a_4955_);
lean_inc(v_a_4954_);
lean_inc_ref(v_a_4953_);
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4944_);
v___x_4960_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4944_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v_fst_4962_; lean_object* v___x_4963_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref(v___x_4960_);
v_fst_4962_ = lean_ctor_get(v_a_4961_, 0);
lean_inc(v_fst_4962_);
lean_dec(v_a_4961_);
lean_inc(v_a_4956_);
lean_inc_ref(v_a_4955_);
lean_inc(v_a_4954_);
lean_inc_ref(v_a_4953_);
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_inc_ref(v_b_4945_);
v___x_4963_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v_fst_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_5048_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref(v___x_4963_);
v_fst_4965_ = lean_ctor_get(v_a_4964_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_a_4964_);
if (v_isSharedCheck_5048_ == 0)
{
lean_object* v_unused_5049_; 
v_unused_5049_ = lean_ctor_get(v_a_4964_, 1);
lean_dec(v_unused_5049_);
v___x_4967_ = v_a_4964_;
v_isShared_4968_ = v_isSharedCheck_5048_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_fst_4965_);
lean_dec(v_a_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_5048_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4969_; 
v___x_4969_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4944_, v_a_4947_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v_id_4971_; lean_object* v_structId_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref(v___x_4969_);
v_id_4971_ = lean_ctor_get(v_a_4959_, 0);
lean_inc(v_id_4971_);
v_structId_4972_ = lean_ctor_get(v_a_4959_, 1);
lean_inc(v_structId_4972_);
lean_dec(v_a_4959_);
v___x_4973_ = 0;
lean_inc(v_a_4956_);
lean_inc_ref(v_a_4955_);
lean_inc(v_a_4954_);
lean_inc_ref(v_a_4953_);
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_inc(v_structId_4972_);
v___x_4974_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4962_, v___x_4973_, v_a_4970_, v_structId_4972_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5031_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_5031_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5031_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
if (lean_obj_tag(v_a_4975_) == 1)
{
lean_object* v_val_4979_; lean_object* v___x_4980_; 
lean_del_object(v___x_4977_);
v_val_4979_ = lean_ctor_get(v_a_4975_, 0);
lean_inc(v_val_4979_);
lean_dec_ref(v_a_4975_);
v___x_4980_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4945_, v_a_4947_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4982_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref(v___x_4980_);
lean_inc(v_a_4956_);
lean_inc_ref(v_a_4955_);
lean_inc(v_a_4954_);
lean_inc_ref(v_a_4953_);
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_inc(v_structId_4972_);
v___x_4982_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4965_, v___x_4973_, v_a_4981_, v_structId_4972_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5010_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_5010_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5010_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
if (lean_obj_tag(v_a_4983_) == 1)
{
lean_object* v_val_4987_; lean_object* v___x_4989_; 
v_val_4987_ = lean_ctor_get(v_a_4983_, 0);
lean_inc(v_val_4987_);
lean_dec_ref(v_a_4983_);
lean_inc(v_val_4987_);
lean_inc(v_val_4979_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set_tag(v___x_4967_, 3);
lean_ctor_set(v___x_4967_, 1, v_val_4987_);
lean_ctor_set(v___x_4967_, 0, v_val_4979_);
v___x_4989_ = v___x_4967_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_val_4979_);
lean_ctor_set(v_reuseFailAlloc_5005_, 1, v_val_4987_);
v___x_4989_ = v_reuseFailAlloc_5005_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v___x_4990_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4989_);
v___x_4991_ = lean_box(0);
v___x_4992_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4990_, v___x_4991_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_del_object(v___x_4985_);
lean_inc(v_val_4987_);
lean_inc(v_val_4979_);
lean_inc(v_id_4971_);
lean_inc_ref(v_b_4945_);
lean_inc_ref(v_a_4944_);
v___x_4993_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4993_, 0, v_a_4944_);
lean_ctor_set(v___x_4993_, 1, v_b_4945_);
lean_ctor_set(v___x_4993_, 2, v_id_4971_);
lean_ctor_set(v___x_4993_, 3, v_val_4979_);
lean_ctor_set(v___x_4993_, 4, v_val_4987_);
lean_inc(v___x_4990_);
v___x_4994_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4994_, 0, v___x_4990_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
lean_ctor_set_uint8(v___x_4994_, sizeof(void*)*2, v___x_4973_);
lean_inc(v_a_4956_);
lean_inc_ref(v_a_4955_);
lean_inc(v_a_4954_);
lean_inc_ref(v_a_4953_);
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_inc(v_structId_4972_);
v___x_4995_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4994_, v_structId_4972_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec_ref(v___x_4995_);
v___x_4996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4997_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4990_, v___x_4996_);
v___x_4998_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4998_, 0, v_b_4945_);
lean_ctor_set(v___x_4998_, 1, v_a_4944_);
lean_ctor_set(v___x_4998_, 2, v_id_4971_);
lean_ctor_set(v___x_4998_, 3, v_val_4987_);
lean_ctor_set(v___x_4998_, 4, v_val_4979_);
v___x_4999_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*2, v___x_4973_);
v___x_5000_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4999_, v_structId_4972_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
return v___x_5000_;
}
else
{
lean_dec(v___x_4990_);
lean_dec(v_val_4987_);
lean_dec(v_val_4979_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
return v___x_4995_;
}
}
else
{
lean_object* v___x_5001_; lean_object* v___x_5003_; 
lean_dec(v___x_4990_);
lean_dec(v_val_4987_);
lean_dec(v_val_4979_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_5001_ = lean_box(0);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5001_);
v___x_5003_ = v___x_4985_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5008_; 
lean_dec(v_a_4983_);
lean_dec(v_val_4979_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_del_object(v___x_4967_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_5006_ = lean_box(0);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5006_);
v___x_5008_ = v___x_4985_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5006_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
else
{
lean_object* v_a_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5018_; 
lean_dec(v_val_4979_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_del_object(v___x_4967_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5011_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_5013_ = v___x_4982_;
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_a_5011_);
lean_dec(v___x_4982_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5016_; 
if (v_isShared_5014_ == 0)
{
v___x_5016_ = v___x_5013_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5011_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec(v_val_4979_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5019_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4980_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4980_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5029_; 
lean_dec(v_a_4975_);
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_5027_ = lean_box(0);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v___x_5027_);
v___x_5029_ = v___x_4977_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec(v_structId_4972_);
lean_dec(v_id_4971_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5032_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_4974_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_4974_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_dec(v_fst_4962_);
lean_dec(v_a_4959_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5040_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4969_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4969_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_fst_4962_);
lean_dec(v_a_4959_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5050_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_4963_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_4963_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec(v_a_4959_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5058_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_4960_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_4960_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5066_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_4958_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_4958_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_5074_, lean_object* v_b_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5074_, v_b_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5089_, lean_object* v_b_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; lean_object* v___x_5105_; 
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5104_);
lean_dec_ref(v___x_5103_);
lean_inc(v_a_5101_);
lean_inc_ref(v_a_5100_);
lean_inc(v_a_5099_);
lean_inc_ref(v_a_5098_);
lean_inc(v_a_5097_);
lean_inc_ref(v_a_5096_);
lean_inc(v_a_5095_);
lean_inc_ref(v_a_5094_);
lean_inc(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc(v_a_5091_);
lean_inc_ref(v_a_5089_);
v___x_5105_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5089_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v_fst_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5203_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5106_);
lean_dec_ref(v___x_5105_);
v_fst_5107_ = lean_ctor_get(v_a_5106_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_a_5106_);
if (v_isSharedCheck_5203_ == 0)
{
lean_object* v_unused_5204_; 
v_unused_5204_ = lean_ctor_get(v_a_5106_, 1);
lean_dec(v_unused_5204_);
v___x_5109_ = v_a_5106_;
v_isShared_5110_ = v_isSharedCheck_5203_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_fst_5107_);
lean_dec(v_a_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5203_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5111_; 
lean_inc(v_a_5101_);
lean_inc_ref(v_a_5100_);
lean_inc(v_a_5099_);
lean_inc_ref(v_a_5098_);
lean_inc(v_a_5097_);
lean_inc_ref(v_a_5096_);
lean_inc(v_a_5095_);
lean_inc_ref(v_a_5094_);
lean_inc(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc_ref(v_b_5090_);
v___x_5111_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v_fst_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5193_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref(v___x_5111_);
v_fst_5113_ = lean_ctor_get(v_a_5112_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v_a_5112_);
if (v_isSharedCheck_5193_ == 0)
{
lean_object* v_unused_5194_; 
v_unused_5194_ = lean_ctor_get(v_a_5112_, 1);
lean_dec(v_unused_5194_);
v___x_5115_ = v_a_5112_;
v_isShared_5116_ = v_isSharedCheck_5193_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_fst_5113_);
lean_dec(v_a_5112_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5193_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; 
v___x_5117_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5089_, v_a_5092_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v_id_5119_; lean_object* v_structId_5120_; uint8_t v___x_5121_; lean_object* v___x_5122_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref(v___x_5117_);
v_id_5119_ = lean_ctor_get(v_a_5104_, 0);
lean_inc(v_id_5119_);
v_structId_5120_ = lean_ctor_get(v_a_5104_, 1);
lean_inc(v_structId_5120_);
lean_dec(v_a_5104_);
v___x_5121_ = 0;
lean_inc(v_a_5101_);
lean_inc_ref(v_a_5100_);
lean_inc(v_a_5099_);
lean_inc_ref(v_a_5098_);
lean_inc(v_a_5097_);
lean_inc_ref(v_a_5096_);
lean_inc(v_a_5095_);
lean_inc_ref(v_a_5094_);
lean_inc(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc(v_structId_5120_);
v___x_5122_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5107_, v___x_5121_, v_a_5118_, v_structId_5120_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5176_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5176_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5176_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
if (lean_obj_tag(v_a_5123_) == 1)
{
lean_object* v_val_5127_; lean_object* v___x_5128_; 
lean_del_object(v___x_5125_);
v_val_5127_ = lean_ctor_get(v_a_5123_, 0);
lean_inc(v_val_5127_);
lean_dec_ref(v_a_5123_);
v___x_5128_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5090_, v_a_5092_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_a_5129_; lean_object* v___x_5130_; 
v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
lean_inc(v_a_5129_);
lean_dec_ref(v___x_5128_);
lean_inc(v_a_5101_);
lean_inc_ref(v_a_5100_);
lean_inc(v_a_5099_);
lean_inc_ref(v_a_5098_);
lean_inc(v_a_5097_);
lean_inc_ref(v_a_5096_);
lean_inc(v_a_5095_);
lean_inc_ref(v_a_5094_);
lean_inc(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc(v_structId_5120_);
v___x_5130_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5113_, v___x_5121_, v_a_5129_, v_structId_5120_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5155_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5133_ = v___x_5130_;
v_isShared_5134_ = v_isSharedCheck_5155_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_5130_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5155_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
if (lean_obj_tag(v_a_5131_) == 1)
{
lean_object* v_val_5135_; lean_object* v___x_5137_; 
v_val_5135_ = lean_ctor_get(v_a_5131_, 0);
lean_inc(v_val_5135_);
lean_dec_ref(v_a_5131_);
lean_inc(v_val_5135_);
lean_inc(v_val_5127_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set_tag(v___x_5115_, 3);
lean_ctor_set(v___x_5115_, 1, v_val_5135_);
lean_ctor_set(v___x_5115_, 0, v_val_5127_);
v___x_5137_ = v___x_5115_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_val_5127_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_val_5135_);
v___x_5137_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
v___x_5138_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5137_);
v___x_5139_ = lean_box(0);
v___x_5140_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5138_, v___x_5139_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
lean_del_object(v___x_5133_);
v___x_5141_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5141_, 0, v_a_5089_);
lean_ctor_set(v___x_5141_, 1, v_b_5090_);
lean_ctor_set(v___x_5141_, 2, v_id_5119_);
lean_ctor_set(v___x_5141_, 3, v_val_5127_);
lean_ctor_set(v___x_5141_, 4, v_val_5135_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 1, v___x_5141_);
lean_ctor_set(v___x_5109_, 0, v___x_5138_);
v___x_5143_ = v___x_5109_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5138_);
lean_ctor_set(v_reuseFailAlloc_5145_, 1, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5143_, v_structId_5120_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
return v___x_5144_;
}
}
else
{
lean_object* v___x_5146_; lean_object* v___x_5148_; 
lean_dec(v___x_5138_);
lean_dec(v_val_5135_);
lean_dec(v_val_5127_);
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v___x_5146_ = lean_box(0);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5146_);
v___x_5148_ = v___x_5133_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5146_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5153_; 
lean_dec(v_a_5131_);
lean_dec(v_val_5127_);
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v___x_5151_ = lean_box(0);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5151_);
v___x_5153_ = v___x_5133_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec(v_val_5127_);
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5156_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5130_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5130_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec(v_val_5127_);
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5115_);
lean_dec(v_fst_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5164_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5128_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5128_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5174_; 
lean_dec(v_a_5123_);
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5115_);
lean_dec(v_fst_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v___x_5172_ = lean_box(0);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v___x_5172_);
v___x_5174_ = v___x_5125_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
lean_dec(v_structId_5120_);
lean_dec(v_id_5119_);
lean_del_object(v___x_5115_);
lean_dec(v_fst_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5177_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5122_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5122_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
lean_del_object(v___x_5115_);
lean_dec(v_fst_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_fst_5107_);
lean_dec(v_a_5104_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5185_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5117_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5117_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_del_object(v___x_5109_);
lean_dec(v_fst_5107_);
lean_dec(v_a_5104_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5195_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5111_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5111_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_dec(v_a_5104_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec(v_a_5091_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5205_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5105_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5105_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec(v_a_5091_);
lean_dec_ref(v_b_5090_);
lean_dec_ref(v_a_5089_);
v_a_5213_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5103_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5103_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5221_, lean_object* v_b_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5221_, v_b_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5236_, lean_object* v_b_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_){
_start:
{
uint8_t v___x_5249_; 
v___x_5249_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5236_, v_b_5237_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; 
v___x_5250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5236_, v_b_5237_, v_a_5238_, v_a_5246_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc(v_a_5251_);
lean_dec_ref(v___x_5250_);
if (lean_obj_tag(v_a_5251_) == 1)
{
lean_object* v_val_5252_; lean_object* v___x_5253_; 
v_val_5252_ = lean_ctor_get(v_a_5251_, 0);
lean_inc(v_val_5252_);
lean_dec_ref(v_a_5251_);
v___x_5253_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; uint8_t v___x_5255_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
lean_inc(v_a_5254_);
lean_dec_ref(v___x_5253_);
v___x_5255_ = lean_unbox(v_a_5254_);
lean_dec(v_a_5254_);
if (v___x_5255_ == 0)
{
lean_object* v___x_5256_; 
v___x_5256_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; uint8_t v___x_5258_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_a_5257_);
lean_dec_ref(v___x_5256_);
v___x_5258_ = lean_unbox(v_a_5257_);
lean_dec(v_a_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
v___x_5259_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5236_, v_b_5237_, v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5259_;
}
else
{
lean_object* v___x_5260_; 
lean_dec(v_val_5252_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
v___x_5260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5236_, v_b_5237_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
return v___x_5260_;
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec(v_val_5252_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5261_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5256_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5256_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v___x_5269_; 
v___x_5269_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; uint8_t v___x_5271_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
lean_dec_ref(v___x_5269_);
v___x_5271_ = lean_unbox(v_a_5270_);
lean_dec(v_a_5270_);
if (v___x_5271_ == 0)
{
lean_object* v___x_5272_; 
v___x_5272_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5236_, v_b_5237_, v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5272_;
}
else
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5236_, v_b_5237_, v_val_5252_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5273_;
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec(v_val_5252_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5274_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5269_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5269_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5289_; 
lean_dec(v_val_5252_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5282_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5284_ = v___x_5253_;
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5253_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5287_; 
if (v_isShared_5285_ == 0)
{
v___x_5287_ = v___x_5284_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
}
else
{
lean_object* v___x_5290_; 
lean_dec(v_a_5251_);
v___x_5290_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5236_, v_b_5237_, v_a_5238_, v_a_5246_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5313_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5313_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5313_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
if (lean_obj_tag(v_a_5291_) == 1)
{
lean_object* v_val_5295_; lean_object* v___x_5296_; 
lean_del_object(v___x_5293_);
v_val_5295_ = lean_ctor_get(v_a_5291_, 0);
lean_inc(v_val_5295_);
lean_dec_ref(v_a_5291_);
v___x_5296_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5295_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; lean_object* v_orderedAddInst_x3f_5298_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_a_5297_);
lean_dec_ref(v___x_5296_);
v_orderedAddInst_x3f_5298_ = lean_ctor_get(v_a_5297_, 9);
lean_inc(v_orderedAddInst_x3f_5298_);
lean_dec(v_a_5297_);
if (lean_obj_tag(v_orderedAddInst_x3f_5298_) == 0)
{
lean_object* v___x_5299_; 
v___x_5299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5236_, v_b_5237_, v_val_5295_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5299_;
}
else
{
lean_object* v___x_5300_; 
lean_dec_ref(v_orderedAddInst_x3f_5298_);
v___x_5300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5236_, v_b_5237_, v_val_5295_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5300_;
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_dec(v_val_5295_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5301_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5296_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5296_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
else
{
lean_object* v___x_5309_; lean_object* v___x_5311_; 
lean_dec(v_a_5291_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v___x_5309_ = lean_box(0);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v___x_5309_);
v___x_5311_ = v___x_5293_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5314_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5290_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5290_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v_a_5322_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5250_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5250_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
else
{
lean_object* v___x_5330_; lean_object* v___x_5331_; 
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_b_5237_);
lean_dec_ref(v_a_5236_);
v___x_5330_ = lean_box(0);
v___x_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5330_);
return v___x_5331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5332_, lean_object* v_b_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5332_, v_b_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5346_, lean_object* v_b_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
uint8_t v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5360_ = 0;
v___x_5361_ = lean_unsigned_to_nat(0u);
v___x_5362_ = lean_box(v___x_5360_);
lean_inc_ref(v_a_5346_);
v___x_5363_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5363_, 0, v_a_5346_);
lean_closure_set(v___x_5363_, 1, v___x_5362_);
lean_closure_set(v___x_5363_, 2, v___x_5361_);
lean_inc(v_a_5358_);
lean_inc_ref(v_a_5357_);
lean_inc(v_a_5356_);
lean_inc_ref(v_a_5355_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
v___x_5364_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5363_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5466_; 
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5367_ = v___x_5364_;
v_isShared_5368_ = v_isSharedCheck_5466_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5364_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5466_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
if (lean_obj_tag(v_a_5365_) == 1)
{
lean_object* v_val_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; 
lean_del_object(v___x_5367_);
v_val_5369_ = lean_ctor_get(v_a_5365_, 0);
lean_inc(v_val_5369_);
lean_dec_ref(v_a_5365_);
v___x_5370_ = lean_box(v___x_5360_);
lean_inc_ref(v_b_5347_);
v___x_5371_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5371_, 0, v_b_5347_);
lean_closure_set(v___x_5371_, 1, v___x_5370_);
lean_closure_set(v___x_5371_, 2, v___x_5361_);
lean_inc(v_a_5358_);
lean_inc_ref(v_a_5357_);
lean_inc(v_a_5356_);
lean_inc_ref(v_a_5355_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
v___x_5372_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5371_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5453_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5375_ = v___x_5372_;
v_isShared_5376_ = v_isSharedCheck_5453_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5372_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5453_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
if (lean_obj_tag(v_a_5373_) == 1)
{
lean_object* v_val_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
lean_del_object(v___x_5375_);
v_val_5377_ = lean_ctor_get(v_a_5373_, 0);
lean_inc(v_val_5377_);
lean_dec_ref(v_a_5373_);
lean_inc(v_val_5377_);
lean_inc(v_val_5369_);
v___x_5378_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5378_, 0, v_val_5369_);
lean_ctor_set(v___x_5378_, 1, v_val_5377_);
v___x_5379_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5378_);
lean_inc_ref(v_b_5347_);
lean_inc_ref(v_a_5346_);
v___x_5380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5380_, 0, v_a_5346_);
lean_ctor_set(v___x_5380_, 1, v_b_5347_);
lean_ctor_set(v___x_5380_, 2, v_val_5369_);
lean_ctor_set(v___x_5380_, 3, v_val_5377_);
v___x_5381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5379_);
lean_ctor_set(v___x_5381_, 1, v___x_5380_);
lean_inc(v_a_5358_);
lean_inc_ref(v_a_5357_);
lean_inc(v_a_5356_);
lean_inc_ref(v_a_5355_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
v___x_5382_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5381_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5382_) == 0)
{
lean_object* v_a_5383_; lean_object* v___x_5384_; 
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
lean_inc(v_a_5383_);
lean_dec_ref(v___x_5382_);
v___x_5384_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5346_, v_a_5349_);
lean_dec_ref(v_a_5346_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v_a_5385_; lean_object* v___x_5386_; 
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
lean_inc(v_a_5385_);
lean_dec_ref(v___x_5384_);
v___x_5386_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5347_, v_a_5349_);
lean_dec_ref(v_b_5347_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; lean_object* v_p_5388_; lean_object* v___y_5390_; uint8_t v___x_5424_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref(v___x_5386_);
v_p_5388_ = lean_ctor_get(v_a_5383_, 0);
v___x_5424_ = lean_nat_dec_le(v_a_5385_, v_a_5387_);
if (v___x_5424_ == 0)
{
lean_dec(v_a_5387_);
v___y_5390_ = v_a_5385_;
goto v___jp_5389_;
}
else
{
lean_dec(v_a_5385_);
v___y_5390_ = v_a_5387_;
goto v___jp_5389_;
}
v___jp_5389_:
{
lean_object* v___x_5391_; 
lean_inc(v_a_5358_);
lean_inc_ref(v_a_5357_);
lean_inc(v_a_5356_);
lean_inc_ref(v_a_5355_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
lean_inc(v___y_5390_);
lean_inc_ref(v_p_5388_);
v___x_5391_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5388_, v___y_5390_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5393_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
lean_inc(v_a_5392_);
lean_dec_ref(v___x_5391_);
lean_inc(v_a_5358_);
lean_inc_ref(v_a_5357_);
lean_inc(v_a_5356_);
lean_inc_ref(v_a_5355_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
lean_inc(v_a_5348_);
v___x_5393_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5392_, v___x_5360_, v___y_5390_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5407_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5396_ = v___x_5393_;
v_isShared_5397_ = v_isSharedCheck_5407_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5393_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5407_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
if (lean_obj_tag(v_a_5394_) == 1)
{
lean_object* v_val_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_del_object(v___x_5396_);
v_val_5398_ = lean_ctor_get(v_a_5394_, 0);
lean_inc(v_val_5398_);
lean_dec_ref(v_a_5394_);
lean_inc(v_val_5398_);
v___x_5399_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5398_);
v___x_5400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5400_, 0, v_a_5383_);
lean_ctor_set(v___x_5400_, 1, v_val_5398_);
v___x_5401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5399_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5401_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
return v___x_5402_;
}
else
{
lean_object* v___x_5403_; lean_object* v___x_5405_; 
lean_dec(v_a_5394_);
lean_dec(v_a_5383_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
v___x_5403_ = lean_box(0);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v___x_5403_);
v___x_5405_ = v___x_5396_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec(v_a_5383_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
v_a_5408_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5393_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5393_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec(v___y_5390_);
lean_dec(v_a_5383_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
v_a_5416_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5391_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5391_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec(v_a_5385_);
lean_dec(v_a_5383_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
v_a_5425_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5386_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5386_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
lean_dec(v_a_5383_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
v_a_5433_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v___x_5384_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5384_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
else
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5448_; 
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
lean_dec_ref(v_a_5346_);
v_a_5441_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5448_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v___x_5382_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5382_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5446_; 
if (v_isShared_5444_ == 0)
{
v___x_5446_ = v___x_5443_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
else
{
lean_object* v___x_5449_; lean_object* v___x_5451_; 
lean_dec(v_a_5373_);
lean_dec(v_val_5369_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
lean_dec_ref(v_a_5346_);
v___x_5449_ = lean_box(0);
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v___x_5449_);
v___x_5451_ = v___x_5375_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v___x_5449_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
lean_dec(v_val_5369_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
lean_dec_ref(v_a_5346_);
v_a_5454_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5372_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5372_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
else
{
lean_object* v___x_5462_; lean_object* v___x_5464_; 
lean_dec(v_a_5365_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
lean_dec_ref(v_a_5346_);
v___x_5462_ = lean_box(0);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v___x_5462_);
v___x_5464_ = v___x_5367_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5462_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
else
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5474_; 
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_b_5347_);
lean_dec_ref(v_a_5346_);
v_a_5467_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5469_ = v___x_5364_;
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5364_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5472_; 
if (v_isShared_5470_ == 0)
{
v___x_5472_ = v___x_5469_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5475_, lean_object* v_b_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5475_, v_b_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5490_, lean_object* v_b_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_){
_start:
{
lean_object* v___x_5504_; 
v___x_5504_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5490_, v_a_5493_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; uint8_t v___x_5506_; lean_object* v___x_5507_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5505_);
lean_dec_ref(v___x_5504_);
v___x_5506_ = 0;
lean_inc(v_a_5502_);
lean_inc_ref(v_a_5501_);
lean_inc(v_a_5500_);
lean_inc_ref(v_a_5499_);
lean_inc(v_a_5498_);
lean_inc_ref(v_a_5497_);
lean_inc(v_a_5496_);
lean_inc_ref(v_a_5495_);
lean_inc(v_a_5494_);
lean_inc(v_a_5493_);
lean_inc(v_a_5492_);
lean_inc_ref(v_a_5490_);
v___x_5507_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5490_, v___x_5506_, v_a_5505_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5551_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5510_ = v___x_5507_;
v_isShared_5511_ = v_isSharedCheck_5551_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5507_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5551_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
if (lean_obj_tag(v_a_5508_) == 1)
{
lean_object* v_val_5512_; lean_object* v___x_5513_; 
lean_del_object(v___x_5510_);
v_val_5512_ = lean_ctor_get(v_a_5508_, 0);
lean_inc(v_val_5512_);
lean_dec_ref(v_a_5508_);
v___x_5513_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5491_, v_a_5493_);
if (lean_obj_tag(v___x_5513_) == 0)
{
lean_object* v_a_5514_; lean_object* v___x_5515_; 
v_a_5514_ = lean_ctor_get(v___x_5513_, 0);
lean_inc(v_a_5514_);
lean_dec_ref(v___x_5513_);
lean_inc(v_a_5502_);
lean_inc_ref(v_a_5501_);
lean_inc(v_a_5500_);
lean_inc_ref(v_a_5499_);
lean_inc(v_a_5498_);
lean_inc_ref(v_a_5497_);
lean_inc(v_a_5496_);
lean_inc_ref(v_a_5495_);
lean_inc(v_a_5494_);
lean_inc(v_a_5493_);
lean_inc(v_a_5492_);
lean_inc_ref(v_b_5491_);
v___x_5515_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5491_, v___x_5506_, v_a_5514_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
if (lean_obj_tag(v___x_5515_) == 0)
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5530_; 
v_a_5516_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5518_ = v___x_5515_;
v_isShared_5519_ = v_isSharedCheck_5530_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5515_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5530_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
if (lean_obj_tag(v_a_5516_) == 1)
{
lean_object* v_val_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
lean_del_object(v___x_5518_);
v_val_5520_ = lean_ctor_get(v_a_5516_, 0);
lean_inc(v_val_5520_);
lean_dec_ref(v_a_5516_);
lean_inc(v_val_5520_);
lean_inc(v_val_5512_);
v___x_5521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5521_, 0, v_val_5512_);
lean_ctor_set(v___x_5521_, 1, v_val_5520_);
v___x_5522_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5521_);
v___x_5523_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5523_, 0, v_a_5490_);
lean_ctor_set(v___x_5523_, 1, v_b_5491_);
lean_ctor_set(v___x_5523_, 2, v_val_5512_);
lean_ctor_set(v___x_5523_, 3, v_val_5520_);
v___x_5524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5522_);
lean_ctor_set(v___x_5524_, 1, v___x_5523_);
v___x_5525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5524_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
return v___x_5525_;
}
else
{
lean_object* v___x_5526_; lean_object* v___x_5528_; 
lean_dec(v_a_5516_);
lean_dec(v_val_5512_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v___x_5526_ = lean_box(0);
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 0, v___x_5526_);
v___x_5528_ = v___x_5518_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec(v_val_5512_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v_a_5531_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5515_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5515_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec(v_val_5512_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v_a_5539_ = lean_ctor_get(v___x_5513_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5513_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5513_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5513_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v___x_5547_; lean_object* v___x_5549_; 
lean_dec(v_a_5508_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v___x_5547_ = lean_box(0);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 0, v___x_5547_);
v___x_5549_ = v___x_5510_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5547_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5559_; 
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v_a_5552_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5554_ = v___x_5507_;
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v___x_5507_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___x_5557_; 
if (v_isShared_5555_ == 0)
{
v___x_5557_ = v___x_5554_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_b_5491_);
lean_dec_ref(v_a_5490_);
v_a_5560_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5504_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5504_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5568_, lean_object* v_b_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5568_, v_b_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5583_, lean_object* v_b_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_){
_start:
{
lean_object* v___x_5597_; 
v___x_5597_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v_addRightCancelInst_x3f_5599_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc(v_a_5598_);
lean_dec_ref(v___x_5597_);
v_addRightCancelInst_x3f_5599_ = lean_ctor_get(v_a_5598_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5599_) == 0)
{
lean_object* v___x_5600_; 
lean_dec(v_a_5598_);
v___x_5600_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5583_, v_b_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
lean_dec(v_a_5585_);
return v___x_5600_;
}
else
{
lean_object* v_id_5601_; lean_object* v_structId_5602_; lean_object* v___x_5603_; 
v_id_5601_ = lean_ctor_get(v_a_5598_, 0);
lean_inc(v_id_5601_);
v_structId_5602_ = lean_ctor_get(v_a_5598_, 1);
lean_inc(v_structId_5602_);
lean_dec(v_a_5598_);
lean_inc(v_a_5595_);
lean_inc_ref(v_a_5594_);
lean_inc(v_a_5593_);
lean_inc_ref(v_a_5592_);
lean_inc(v_a_5591_);
lean_inc_ref(v_a_5590_);
lean_inc(v_a_5589_);
lean_inc_ref(v_a_5588_);
lean_inc(v_a_5587_);
lean_inc(v_a_5586_);
lean_inc(v_a_5585_);
lean_inc_ref(v_a_5583_);
v___x_5603_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5583_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v_a_5604_; lean_object* v_fst_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5693_; 
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_a_5604_);
lean_dec_ref(v___x_5603_);
v_fst_5605_ = lean_ctor_get(v_a_5604_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v_a_5604_);
if (v_isSharedCheck_5693_ == 0)
{
lean_object* v_unused_5694_; 
v_unused_5694_ = lean_ctor_get(v_a_5604_, 1);
lean_dec(v_unused_5694_);
v___x_5607_ = v_a_5604_;
v_isShared_5608_ = v_isSharedCheck_5693_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_fst_5605_);
lean_dec(v_a_5604_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5693_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5609_; 
lean_inc(v_a_5595_);
lean_inc_ref(v_a_5594_);
lean_inc(v_a_5593_);
lean_inc_ref(v_a_5592_);
lean_inc(v_a_5591_);
lean_inc_ref(v_a_5590_);
lean_inc(v_a_5589_);
lean_inc_ref(v_a_5588_);
lean_inc(v_a_5587_);
lean_inc(v_a_5586_);
lean_inc_ref(v_b_5584_);
v___x_5609_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v_a_5610_; lean_object* v_fst_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5683_; 
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
lean_inc(v_a_5610_);
lean_dec_ref(v___x_5609_);
v_fst_5611_ = lean_ctor_get(v_a_5610_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_a_5610_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; 
v_unused_5684_ = lean_ctor_get(v_a_5610_, 1);
lean_dec(v_unused_5684_);
v___x_5613_ = v_a_5610_;
v_isShared_5614_ = v_isSharedCheck_5683_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_fst_5611_);
lean_dec(v_a_5610_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5683_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5615_; 
v___x_5615_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5583_, v_a_5586_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v_a_5616_; uint8_t v___x_5617_; lean_object* v___x_5618_; 
v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
lean_inc(v_a_5616_);
lean_dec_ref(v___x_5615_);
v___x_5617_ = 0;
lean_inc(v_a_5595_);
lean_inc_ref(v_a_5594_);
lean_inc(v_a_5593_);
lean_inc_ref(v_a_5592_);
lean_inc(v_a_5591_);
lean_inc_ref(v_a_5590_);
lean_inc(v_a_5589_);
lean_inc_ref(v_a_5588_);
lean_inc(v_a_5587_);
lean_inc(v_a_5586_);
lean_inc(v_structId_5602_);
v___x_5618_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5605_, v___x_5617_, v_a_5616_, v_structId_5602_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5666_; 
v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5621_ = v___x_5618_;
v_isShared_5622_ = v_isSharedCheck_5666_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5618_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5666_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
if (lean_obj_tag(v_a_5619_) == 1)
{
lean_object* v_val_5623_; lean_object* v___x_5624_; 
lean_del_object(v___x_5621_);
v_val_5623_ = lean_ctor_get(v_a_5619_, 0);
lean_inc(v_val_5623_);
lean_dec_ref(v_a_5619_);
v___x_5624_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5584_, v_a_5586_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_object* v_a_5625_; lean_object* v___x_5626_; 
v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
lean_inc(v_a_5625_);
lean_dec_ref(v___x_5624_);
lean_inc(v_a_5595_);
lean_inc_ref(v_a_5594_);
lean_inc(v_a_5593_);
lean_inc_ref(v_a_5592_);
lean_inc(v_a_5591_);
lean_inc_ref(v_a_5590_);
lean_inc(v_a_5589_);
lean_inc_ref(v_a_5588_);
lean_inc(v_a_5587_);
lean_inc(v_a_5586_);
lean_inc(v_structId_5602_);
v___x_5626_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5611_, v___x_5617_, v_a_5625_, v_structId_5602_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5645_; 
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5629_ = v___x_5626_;
v_isShared_5630_ = v_isSharedCheck_5645_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5626_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5645_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
if (lean_obj_tag(v_a_5627_) == 1)
{
lean_object* v_val_5631_; lean_object* v___x_5633_; 
lean_del_object(v___x_5629_);
v_val_5631_ = lean_ctor_get(v_a_5627_, 0);
lean_inc(v_val_5631_);
lean_dec_ref(v_a_5627_);
lean_inc(v_val_5631_);
lean_inc(v_val_5623_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set_tag(v___x_5613_, 3);
lean_ctor_set(v___x_5613_, 1, v_val_5631_);
lean_ctor_set(v___x_5613_, 0, v_val_5623_);
v___x_5633_ = v___x_5613_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_val_5623_);
lean_ctor_set(v_reuseFailAlloc_5640_, 1, v_val_5631_);
v___x_5633_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5637_; 
v___x_5634_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5633_);
v___x_5635_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5635_, 0, v_a_5583_);
lean_ctor_set(v___x_5635_, 1, v_b_5584_);
lean_ctor_set(v___x_5635_, 2, v_id_5601_);
lean_ctor_set(v___x_5635_, 3, v_val_5623_);
lean_ctor_set(v___x_5635_, 4, v_val_5631_);
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 1, v___x_5635_);
lean_ctor_set(v___x_5607_, 0, v___x_5634_);
v___x_5637_ = v___x_5607_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5634_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5635_);
v___x_5637_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
lean_object* v___x_5638_; 
v___x_5638_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5637_, v_structId_5602_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
return v___x_5638_;
}
}
}
else
{
lean_object* v___x_5641_; lean_object* v___x_5643_; 
lean_dec(v_a_5627_);
lean_dec(v_val_5623_);
lean_del_object(v___x_5613_);
lean_del_object(v___x_5607_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v___x_5641_ = lean_box(0);
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 0, v___x_5641_);
v___x_5643_ = v___x_5629_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5641_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
lean_dec(v_val_5623_);
lean_del_object(v___x_5613_);
lean_del_object(v___x_5607_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5646_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5626_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5626_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5646_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
else
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
lean_dec(v_val_5623_);
lean_del_object(v___x_5613_);
lean_dec(v_fst_5611_);
lean_del_object(v___x_5607_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5654_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5624_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5624_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5657_ == 0)
{
v___x_5659_ = v___x_5656_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
else
{
lean_object* v___x_5662_; lean_object* v___x_5664_; 
lean_dec(v_a_5619_);
lean_del_object(v___x_5613_);
lean_dec(v_fst_5611_);
lean_del_object(v___x_5607_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v___x_5662_ = lean_box(0);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 0, v___x_5662_);
v___x_5664_ = v___x_5621_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5662_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
else
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5674_; 
lean_del_object(v___x_5613_);
lean_dec(v_fst_5611_);
lean_del_object(v___x_5607_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5667_ = lean_ctor_get(v___x_5618_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5669_ = v___x_5618_;
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5618_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
if (v_isShared_5670_ == 0)
{
v___x_5672_ = v___x_5669_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5667_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
}
else
{
lean_object* v_a_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5682_; 
lean_del_object(v___x_5613_);
lean_dec(v_fst_5611_);
lean_del_object(v___x_5607_);
lean_dec(v_fst_5605_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5675_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5677_ = v___x_5615_;
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_a_5675_);
lean_dec(v___x_5615_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5680_; 
if (v_isShared_5678_ == 0)
{
v___x_5680_ = v___x_5677_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5675_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
}
}
else
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5692_; 
lean_del_object(v___x_5607_);
lean_dec(v_fst_5605_);
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5685_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5687_ = v___x_5609_;
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5609_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5685_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
lean_dec(v_structId_5602_);
lean_dec(v_id_5601_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec(v_a_5585_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5695_ = lean_ctor_get(v___x_5603_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5603_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5603_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
else
{
lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5710_; 
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
lean_dec(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec(v_a_5585_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5703_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5705_ = v___x_5597_;
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___x_5597_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5708_; 
if (v_isShared_5706_ == 0)
{
v___x_5708_ = v___x_5705_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_a_5703_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5711_, lean_object* v_b_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_){
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5711_, v_b_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
return v_res_5725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5726_, lean_object* v_b_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_){
_start:
{
lean_object* v___x_5739_; 
v___x_5739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5726_, v_b_5727_, v_a_5728_, v_a_5736_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v_a_5740_; 
v_a_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_a_5740_);
lean_dec_ref(v___x_5739_);
if (lean_obj_tag(v_a_5740_) == 1)
{
lean_object* v_val_5741_; lean_object* v___x_5742_; 
v_val_5741_ = lean_ctor_get(v_a_5740_, 0);
lean_inc(v_val_5741_);
lean_dec_ref(v_a_5740_);
v___x_5742_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5741_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; uint8_t v___x_5744_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_a_5743_);
lean_dec_ref(v___x_5742_);
v___x_5744_ = lean_unbox(v_a_5743_);
lean_dec(v_a_5743_);
if (v___x_5744_ == 0)
{
lean_object* v___x_5745_; 
v___x_5745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5726_, v_b_5727_, v_val_5741_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
return v___x_5745_;
}
else
{
lean_object* v___x_5746_; 
v___x_5746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5726_, v_b_5727_, v_val_5741_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
return v___x_5746_;
}
}
else
{
lean_object* v_a_5747_; lean_object* v___x_5749_; uint8_t v_isShared_5750_; uint8_t v_isSharedCheck_5754_; 
lean_dec(v_val_5741_);
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_b_5727_);
lean_dec_ref(v_a_5726_);
v_a_5747_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5749_ = v___x_5742_;
v_isShared_5750_ = v_isSharedCheck_5754_;
goto v_resetjp_5748_;
}
else
{
lean_inc(v_a_5747_);
lean_dec(v___x_5742_);
v___x_5749_ = lean_box(0);
v_isShared_5750_ = v_isSharedCheck_5754_;
goto v_resetjp_5748_;
}
v_resetjp_5748_:
{
lean_object* v___x_5752_; 
if (v_isShared_5750_ == 0)
{
v___x_5752_ = v___x_5749_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_a_5747_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
else
{
lean_object* v___x_5755_; 
lean_dec(v_a_5740_);
v___x_5755_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5726_, v_b_5727_, v_a_5728_, v_a_5736_);
if (lean_obj_tag(v___x_5755_) == 0)
{
lean_object* v_a_5756_; lean_object* v___x_5758_; uint8_t v_isShared_5759_; uint8_t v_isSharedCheck_5766_; 
v_a_5756_ = lean_ctor_get(v___x_5755_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5758_ = v___x_5755_;
v_isShared_5759_ = v_isSharedCheck_5766_;
goto v_resetjp_5757_;
}
else
{
lean_inc(v_a_5756_);
lean_dec(v___x_5755_);
v___x_5758_ = lean_box(0);
v_isShared_5759_ = v_isSharedCheck_5766_;
goto v_resetjp_5757_;
}
v_resetjp_5757_:
{
if (lean_obj_tag(v_a_5756_) == 1)
{
lean_object* v_val_5760_; lean_object* v___x_5761_; 
lean_del_object(v___x_5758_);
v_val_5760_ = lean_ctor_get(v_a_5756_, 0);
lean_inc(v_val_5760_);
lean_dec_ref(v_a_5756_);
v___x_5761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5726_, v_b_5727_, v_val_5760_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
return v___x_5761_;
}
else
{
lean_object* v___x_5762_; lean_object* v___x_5764_; 
lean_dec(v_a_5756_);
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_b_5727_);
lean_dec_ref(v_a_5726_);
v___x_5762_ = lean_box(0);
if (v_isShared_5759_ == 0)
{
lean_ctor_set(v___x_5758_, 0, v___x_5762_);
v___x_5764_ = v___x_5758_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5762_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
}
else
{
lean_object* v_a_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5774_; 
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_b_5727_);
lean_dec_ref(v_a_5726_);
v_a_5767_ = lean_ctor_get(v___x_5755_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5769_ = v___x_5755_;
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_a_5767_);
lean_dec(v___x_5755_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5772_; 
if (v_isShared_5770_ == 0)
{
v___x_5772_ = v___x_5769_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_a_5767_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
}
else
{
lean_object* v_a_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5782_; 
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_b_5727_);
lean_dec_ref(v_a_5726_);
v_a_5775_ = lean_ctor_get(v___x_5739_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5777_ = v___x_5739_;
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_a_5775_);
lean_dec(v___x_5739_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5780_; 
if (v_isShared_5778_ == 0)
{
v___x_5780_ = v___x_5777_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5783_, lean_object* v_b_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5783_, v_b_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_);
return v_res_5796_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
}
#ifdef __cplusplus
}
#endif
